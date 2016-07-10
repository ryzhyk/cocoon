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
{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

-- Managing physical network topology induced by a Cocoon spec

module Topology ( Topology
                , PhyTopology
                , topologyLinks
                , isPort
                , InstanceDescr(..)
                , PortInstDescr(..)
                , InstanceMap(..)
                , instMapFlatten
                , PortLinks
                , PhyPortLinks
                , nodeFromPort
                , portFromNode
                , phyPortNum
                , generateTopology) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Tuple.Select
import Control.Monad.State
import Control.Monad.Except

import Eval
import Syntax
import Name
import NS
import Pos
import Type
import Expr
import Util
import SMT

-- Multidimensional array of switch instances.  Each dimension corresponds to a 
-- key.  Innermost elements enumerate ports of an instance.
newtype InstanceMap a = InstanceMap (Either [(Expr, InstanceMap a)] a)

instMapFlatten :: Node -> InstanceMap a -> [(InstanceDescr, a)]
instMapFlatten node (InstanceMap (Left insts))  = concatMap (\(k, imap) -> map (\(InstanceDescr n keys, links) -> (InstanceDescr n (k:keys), links)) $ instMapFlatten node imap) insts
instMapFlatten node (InstanceMap (Right links)) = [(InstanceDescr (name node) [], links)]

-- ((input_port_name, output_port_name), (first_physical_portnum, last_physical_portnum), (logical_out_port_index -> remote_port))
type PortLinks = [((String, String), (Int, Int), [(Int, Maybe PortInstDescr)])]

type PhyPortLinks = [((String, String), [(Int, Int, Maybe PortInstDescr)])]

-- Role instance descriptor
data InstanceDescr = InstanceDescr {idescNode::String, idescKeys::[Expr]} deriving (Eq, Show)
data PortInstDescr = PortInstDescr {pdescPort::String, pdescKeys::[Expr]} deriving (Eq, Show)

instLinks :: (?r::Refine) => (InstanceDescr, PortLinks) -> [(PortInstDescr, PortInstDescr)]
instLinks (node, plinks) = 
    concatMap (\((_,o), _, links) -> mapMaybe (\(pnum, mpdescr) -> fmap (portFromNode ?r node o pnum,) mpdescr) links) 
              plinks

type Topology = [(Node, InstanceMap PortLinks)]
type PhyTopology = [(Node, InstanceMap PhyPortLinks)]

topologyLinks :: (?r::Refine) => Topology -> [(PortInstDescr, PortInstDescr)]
topologyLinks = concatMap (\(n, imap) -> concatMap instLinks $ instMapFlatten n imap)

getInstPortMap :: Topology -> InstanceDescr -> PortLinks
getInstPortMap t (InstanceDescr ndname keys) = getInstPortMap' (snd $ fromJust $ find ((==ndname) . name . fst) t) keys

getInstPortMap' :: InstanceMap a -> [Expr] -> a
getInstPortMap' (InstanceMap (Left mp))     (k:ks) = getInstPortMap' (fromJust $ lookup k mp) ks
getInstPortMap' (InstanceMap (Right links)) []     = links
getInstPortMap' _ _                                = error "Topology.getInstPortMap': unexpected input"

phyPortNum :: Topology -> InstanceDescr -> String -> Int -> Int
phyPortNum t inst pname pnum = base + pnum
    where plinks = getInstPortMap t inst
          (_, (base, _), _) = fromJust $ find ((\(i,o) -> i == pname || o == pname) . sel1) plinks

isPort :: Refine -> String -> Bool
isPort r pname = isJust $ find (isJust . find (\(i,o) -> i == pname || o == pname) . nodePorts) $ refineNodes r

nodeFromPort :: Refine -> PortInstDescr -> InstanceDescr
nodeFromPort r (PortInstDescr pname keys) = InstanceDescr noderole $ init keys
    where noderole = name $ fromJust $ find (isJust . find (\(i,o) -> i == pname || o == pname) . nodePorts) $ refineNodes r

portFromNode :: Refine -> InstanceDescr -> String -> Int -> PortInstDescr
portFromNode r (InstanceDescr _ ks) pname pnum = PortInstDescr pname (ks++[EInt nopos w $ fromIntegral pnum])
    where prole = getRole r pname
          TUInt _ w = typ' r (CtxRole prole) $ last $ roleKeys prole

generateTopology :: (MonadError String me) => Refine -> me Topology
generateTopology r = do 
    let ?r = r 
    t <- mapM (\n -> liftM (n,) $ mkNodeInstMap n) $ refineNodes r 
    validateTopology t
    return t
                 
-- swap input/output port    
flipPort :: (?r::Refine) => PortInstDescr -> PortInstDescr
flipPort p = p{pdescPort = pname}
    where pname = head 
                  $ mapMaybe (\(i,o) -> if' (i == pdescPort p) (Just o) $ if' (o == pdescPort p) (Just i) Nothing) 
                  $ nodePorts 
                  $ getNode ?r 
                  $ idescNode 
                  $ nodeFromPort ?r p

validateTopology :: (?r::Refine, MonadError String me) => Topology -> me ()
validateTopology t = do
    let links = topologyLinks t
    mapM_ (\(s,d) -> assert (not $ isPort ?r (pdescPort s) && isPort ?r (pdescPort d) &&
                                   (null $ filter (\(s',d') -> s' == flipPort d && d' == flipPort s) links)) nopos 
                            $ "Link " ++ show s ++ "->" ++ show d ++ " does not have a reverse") links
    mapM_ (\(s,_) -> case filter (\(s',_) -> s' == s) links of
                          [_] -> return ()
                          ls  -> err nopos $ "Found multiple outgoing links from port " ++ show s ++ ": " ++ show ls) links

mkNodeInstMap :: (?r::Refine, MonadError String me) => Node -> me (InstanceMap PortLinks)
mkNodeInstMap nd = mkNodeInstMap' nd M.empty (roleKeys $ getRole ?r (name nd))

mkNodeInstMap' :: (?r::Refine, MonadError String me) => Node -> KMap -> [Field] -> me (InstanceMap PortLinks)
mkNodeInstMap' nd kmap []     = liftM (InstanceMap . Right) $ mkNodePortLinks kmap (nodePorts nd) 0
mkNodeInstMap' nd kmap (f:fs) = liftM (InstanceMap . Left) 
                                $ mapM (\e -> liftM (e,) $ mkNodeInstMap' nd (M.insert (name f) e kmap) fs) 
                                $ solveFor ndrole fConstr (name f)
    -- Equation to compute possible values of f from:
    where fConstr = (roleKeyRange ndrole):keyVals
          ndrole = getRole ?r $ nodeName nd
          keyVals = map (\(k,v) -> EBinOp nopos Eq (EVar nopos k) v) $ M.toList kmap

mkNodePortLinks :: (?r::Refine, MonadError String me) => KMap -> [(String,String)] -> Int -> me PortLinks
mkNodePortLinks kmap (ports:ps) base = do 
    links <- mkNodePortLinks' kmap ports 
    let lastport = maximum $ map fst links
    liftM ((ports, (base, base+lastport), links):) $ mkNodePortLinks kmap ps (base+lastport+1)
mkNodePortLinks _ [] _ = return []

mkNodePortLinks' :: (?r::Refine, MonadError String me) => KMap -> (String, String) -> me [(Int, Maybe PortInstDescr)]
mkNodePortLinks' kmap (i,o) = mapM (\e@(EInt _ _ pnum) -> liftM (fromInteger pnum,) $ mkLink outrole (M.insert portKey e kmap))
                                   $ solveFor inrole pConstr portKey 
    -- Equation to compute possible values of port index (last key of the port role):
    where pConstr = (roleKeyRange inrole):keyVals
          inrole = getRole ?r i
          outrole = getRole ?r o
          portKey = name $ last $ roleKeys inrole
          keyVals = map (\(k,v) -> EBinOp nopos Eq (EVar nopos k) v) $ M.toList kmap

-- Compute remote port role is connected to.  Role must be an output port of a switch.
mkLink :: (?r::Refine, MonadError String me) => Role -> KMap -> me (Maybe PortInstDescr)
mkLink role kmap = do
    let ?c    = CtxRole role
    case portSendsTo kmap (roleBody role) of
         []                         -> return Nothing
         [ELocation _ n ks]         -> if all (\k -> (null $ exprFuncs ?r k) && (not $ exprRefersToPkt k)) ks
                                          then return $ Just $ PortInstDescr n ks
                                          else err nopos $ "mkLink: output port " ++ name role ++ " cannot be statically evaluated"
         es                         -> err nopos $ "mkLink: output port " ++ name role ++ " " ++ show kmap ++ " sends to multiple destinations: " ++ show es

-- Evaluate output port body.  Assume that it can only consist of 
-- conditions and send statements, i.e., it cannot modify or clone packets.
portSendsTo :: (?r::Refine, ?c::ECtx) => KMap -> Statement -> [Expr]
portSendsTo kmap = nub . fst . portSendsTo' kmap

portSendsTo' :: (?r::Refine, ?c::ECtx) => KMap -> Statement -> ([Expr], KMap)
portSendsTo' kmap (SSend _ e)     = ([evalExpr kmap e], kmap)
portSendsTo' kmap (SITE _ c t e)  = case evalExpr kmap c of
                                         EBool _ True  -> let (s, _) = portSendsTo' kmap t
                                                          in (s, kmap)
                                         EBool _ False -> case e of
                                                               Nothing -> ([], kmap)
                                                               Just e' -> let (s, _) = portSendsTo' kmap e'
                                                                          in (s, kmap)
                                         _             -> let (s1, _) = portSendsTo' kmap t 
                                                              (s2, _) = maybe ([], kmap) (portSendsTo' kmap) e
                                                          in (s1 ++ s2, kmap)
portSendsTo' kmap (SSeq  _ s1 s2) = case s1 of 
                                         STest _ c   -> case evalExpr kmap c of 
                                                             EBool _ False -> ([], kmap)
                                                             _             -> portSendsTo' kmap s2
                                         _           -> let (send1, kmap')  = portSendsTo' kmap s1
                                                            (send2, kmap'') = portSendsTo' kmap' s2
                                                        in (send1 ++ send2, kmap'')
portSendsTo' kmap (STest _ _)     = ([], kmap)
portSendsTo' kmap (SLet _ _ n v)  = ([], M.insert n (evalExpr kmap v) kmap)
portSendsTo' _    s               = error $ "Topology.portSendsTo' " ++ show s

