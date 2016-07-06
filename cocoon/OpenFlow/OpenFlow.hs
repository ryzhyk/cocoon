{-
Copyrights (c) 2016. Samsung Electronics Ltd. All right reserved. 

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-}
{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

-- Convert Cocoon spec to OpenFlow with Necera extensions

module OpenFlow.OpenFlow(genOFSwitches) where

import qualified Data.Map    as M
import qualified Data.IntMap as IM
import Data.List
import Data.Maybe
import Control.Monad.State

import Syntax
import Topology
import NS
import Name
import Eval
import Util
import Pos
import Expr

-- Number of OpenFlow registers (6 in OVS)
ofNumRegisters :: Int
ofNumRegisters = 6

data Mask = Mask Int Integer

data Value = ValIP4   Integer
           | ValMAC48 Integer
           | ValInt   Int Integer

data OFField = OFInPort
             | OFEthSrc
             | OFEthDst
             | OFRegister Int

data Match = Match { matchField :: OFField
                   , matchMask  :: Maybe Mask
                   , matchVal   :: Value
                   }

data LHS = LHS OFField (Maybe (Int, Int))
data RHS = RHSVar   OFField (Maybe (Int, Int))
         | RHSConst Value

type HTable = Int

data Action = ActionOutput {actPort :: RHS}
            | ActionDrop
            | ActionSet    {actLHS :: LHS, actRHS :: RHS}
            | ActionGoto   {actGotoTable :: HTable}

data Flow = Flow { flowPriority :: Maybe Int
                 , flowMatch    :: [Match]
                 , flowActions  :: [Action]
                 }

data OFTable = OFTable { oftFlows   :: [Flow]
                       , oftDefault :: [Action]
                       }

data OFSwitch = OFSwitch { ofTables :: [OFTable]
                         }


type OFPMap = [((String, String), IM.IntMap Int)]

-- Generator state
data OFState = OFState { ofsTables       :: [OFTable]
                       , ofsNextRegister :: Int
                       , ofsRegisterMap  :: [(Expr, Int)]
                       }

-- Allocate register for a local variable
allocRegister :: State OFState Int
allocRegister = do
    nxt <- gets ofsNextRegister
    modify (\s -> s{ofsNextRegister = nxt + 1})
    return nxt

setRegister :: Expr -> Int -> State OFState ()
setRegister e r = modify (\s -> s{ofsRegisterMap = (e, r) : (ofsRegisterMap s)})

addTable :: OFTable -> State OFState HTable
addTable t = do
    h <- gets $ length . ofsTables
    modify (\s -> s{ofsTables = (ofsTables s) ++ [t]})
    return h

-- Generate all switches in the topology
genOFSwitches :: Refine -> PhyTopology -> [OFSwitch]
genOFSwitches r topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = concatMap (\((i,o),plinks) -> let m = IM.fromList $ map (\(l,p,_) -> (l,p)) plinks
                                                                                                   in [((i,o), m)]) links
                                                          in mkOFSwitch r switch kmap pmap) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology


-- Generate OF switch 
mkOFSwitch :: Refine -> Node -> KMap -> OFPMap -> OFSwitch
mkOFSwitch r switch kmap pmap = 
    let ?r = r in
    let ?pmap = pmap in
    let ?kmap = kmap in
    OFSwitch $ ofsTables $ execState mkOFSwitch' (OFState [] 0 [])

mkOFSwitch' :: (?r::Refine, ?kmap::KMap, ?pmap::OFPMap) => State OFState ()
mkOFSwitch' = do
    regInport <- allocRegister
    mapM_ ((\pname -> let role = getRole ?r pname 
                          pvar = name $ last $ roleKeys role in
                      setRegister (EVar nopos pvar) regInport) . fst . fst) ?pmap
    hSend <- mapM (mkOutputPortMap regInport . snd) ?pmap
    hPortHandlers <- mapM (mkPortHandler regInport hSend . fst . fst) ?pmap
    hInput <- mkInputPortMap regInport hPortHandlers
    return ()

-- Input table: map input port number into logical Cocoon port number 
mkInputPortMap :: (?pmap :: OFPMap) => Int -> [HTable] -> State OFState HTable
mkInputPortMap reg next = do
    let flows = concatMap (mapIdx (\(lport, pport) i -> Flow Nothing
                                                             [Match OFInPort Nothing $ ValInt 32 $ fromIntegral pport] 
                                                             [ ActionSet (LHS (OFRegister reg) Nothing) (RHSConst $ ValInt 32 $ fromIntegral lport)
                                                             , ActionGoto $ next !! i]) 
                          . IM.toList . snd) ?pmap
    addTable $ OFTable flows [ActionDrop]

mkOutputPortMap :: Int -> IM.IntMap Int -> State OFState HTable
mkOutputPortMap reg m = do
    let flows = map (\(lport, pport) -> Flow Nothing
                                             [Match (OFRegister reg) Nothing $ ValInt 32 $ fromIntegral lport] 
                                             [ActionOutput (RHSConst $ ValInt 32 $ fromIntegral pport)]) 
                    $ IM.toList m
    addTable $ OFTable flows [ActionDrop]

mkPortHandler :: (?r::Refine, ?kmap::KMap, ?pmap::OFPMap) => Int -> [HTable] -> String -> State OFState HTable
mkPortHandler regOutPort hSend pname = do
    hDrop <- addTable $ OFTable [] [ActionDrop]
    let ?hSend = hSend
        ?role = getRole ?r pname 
        ?regOutPort = regOutPort
    let ?c = CtxRole ?role
    mkStatement hDrop $ roleBody ?role

mkStatement :: (?r::Refine, ?kmap::KMap, ?pmap::OFPMap, ?role::Role, ?c::ECtx, ?hSend::[HTable], ?regOutPort::Int) => HTable -> Statement -> State OFState HTable
mkStatement next (SSeq    _ l r)    = do next' <- mkStatement next r
                                         mkStatement next' l
mkStatement next (SPar    _ _ _)    = error "Not implemented: OpenFlow.mkStatement: SPar"
mkStatement next (SITE    _ c t me) = do hthen <- mkStatement next t
                                         helse <- maybe (return next) (mkStatement next) me
                                         mkCond c hthen (Just helse)
mkStatement next (STest   _ c)      = mkCond c next Nothing
mkStatement next (SSet    _ l r)    = do let r' = evalExpr ?kmap r
                                         mkStore next r' $ map lexprToLHS $ exprScalars ?r ?c l
mkStatement next (SSend   _ dst)    = do let ELocation _ n ks = evalExpr ?kmap dst
                                             portIdx = fromJust $ findIndex ((== n) . snd . fst) ?pmap
                                         mkStore (?hSend !! portIdx) (last ks) [LHS (OFRegister ?regOutPort) Nothing]
mkStatement next (SSendND _ _ _)    = error "OpenFlow.mkStatement SSendND"
mkStatement next (SHavoc  _ _)      = error "OpenFlow.mkStatement SHavoc" 
mkStatement next (SAssume _ _)      = error "OpenFlow.mkStatement SAssume"
mkStatement next (SLet    _ t n v)  = do let v' = evalExpr ?kmap v
                                         regs <- mapM (\e -> do reg <- allocRegister
                                                                setRegister e reg
                                                                return reg) 
                                                      $ exprScalars ?r ?c $ EVar nopos n
                                         mkStore next v' $ map (\r -> LHS (OFRegister r) Nothing) regs
mkStatement next (SFork   _ vs c b) = undefined

mkStore :: HTable -> Expr -> [LHS] -> State OFState HTable
mkStore = undefined

mkCond :: Expr -> HTable -> Maybe HTable -> State OFState HTable
mkCond = undefined

lexprToLHS :: Expr -> LHS
lexprToLHS = undefined

-- Generate pipeline for each port
-- SSeq: use lazy evaluation to comput the input table of the second statement after generating the first statement
-- SITE: Compile condition into a sequence of tables.  Reserve placeholder tables for undefined functions
-- STest: is a special case of SITE
-- SSet: similar to P4: use intermediate temporary variables when needed
-- SSend: send action
-- SLet: use registers.  Allocate register in advance.  Optimization: don't use registers for constant values
-- SFork: use the first conjunct to generate multicast group.  Use the rest as filters.

-- Final table: map output port name
