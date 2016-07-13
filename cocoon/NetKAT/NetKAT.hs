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

-- Convert Cocoon spec to NetKAT

module NetKAT.NetKAT(genSwitches) where

import Data.Maybe
import Data.List
import qualified Data.Map    as M
import qualified Data.IntMap as IM
import Control.Monad
import Control.Monad.State
import Text.PrettyPrint
import Numeric

import PP
import Topology
import Syntax
import Pos
import Name
import SMT
import Expr
import NS
import Eval
import Type
import Util

data NKHeaderVal = NKEthSrc   Integer
                 | NKEthDst   Integer
                 | NKVlan     Int
                 | NKEthType  Int
                 | NKIPProto  Int
                 | NKIP4Src   Int Int
                 | NKIP4Dst   Int Int
                 | NKLocation Int
                 deriving (Eq, Ord)

ppHeaderVal :: String -> NKHeaderVal -> Doc
ppHeaderVal op (NKEthSrc   mac)    = pp "ethSrc"  <+> pp op <+> ppMAC mac
ppHeaderVal op (NKEthDst   mac)    = pp "ethDst"  <+> pp op <+> ppMAC mac
ppHeaderVal op (NKVlan     vlan)   = pp "vlan"    <+> pp op <+> pp vlan
ppHeaderVal op (NKEthType  etht)   = pp "ethType" <+> pp op <+> pp "0x" <> (pp $ showHex etht "")
ppHeaderVal op (NKIPProto  prot)   = pp "ipProto" <+> pp op <+> pp prot
ppHeaderVal op (NKIP4Src   ip msk) = pp "ip4Src"  <+> pp op <+> ppIP ip msk
ppHeaderVal op (NKIP4Dst   ip msk) = pp "ip4Dst"  <+> pp op <+> ppIP ip msk
ppHeaderVal op (NKLocation port)   = pp "port"    <+> pp op <+> pp port

ppMAC :: Integer -> Doc
ppMAC mac = hcat 
            $ punctuate (char ':') 
            $ map pp
            $ [bitSlice mac 7 0, bitSlice mac 15 8, bitSlice mac 23 16, bitSlice mac 31 24, bitSlice mac 39 32, bitSlice mac 47 40]

ppIP :: Int -> Int -> Doc
ppIP ip msk = (hcat 
               $ punctuate (char '.') 
               $ map pp
               $ [bitSlice ip 7 0, bitSlice ip 15 8, bitSlice ip 23 16, bitSlice ip 31 24]) 
              <> (if' (msk == 32) empty (char '/' <> pp msk))

data NKPred = NKTrue
            | NKFalse
            | NKTest  NKHeaderVal
            | NKAnd   NKPred NKPred
            | NKOr    NKPred NKPred
            | NKNeg   NKPred
            deriving (Eq, Ord)

instance PP NKPred where
    pp NKTrue             = pp "true"
    pp NKFalse            = pp "false"
    pp (NKTest hval)      = ppHeaderVal "=" hval
    pp (NKAnd p1 p2)      = parens $ pp p1 <+> pp "and" <+> pp p2
    pp (NKOr p1 p2)       = parens $ pp p1 <+> pp "or" <+> pp p2
    pp (NKNeg p)          = parens $ pp "not" <+> pp p 

data NKPolicy = NKFilter NKPred
              | NKMod    NKHeaderVal
              | NKUnion  NKPolicy NKPolicy
              | NKSeq    NKPolicy NKPolicy
              | NKITE    NKPred NKPolicy NKPolicy

instance PP NKPolicy where
     pp (NKFilter p)    = pp "filter" <+> pp p
     pp (NKMod hval)    = ppHeaderVal ":=" hval
     pp (NKUnion p1 p2) = parens $ pp p1 $$ pp "|" $$ pp p2
     pp (NKSeq p1 p2)   = parens $ pp p1 <> semi $$ pp p2
     pp (NKITE c t e)   = (pp "if" <+> pp c <+> pp "then")
                          $$ 
                          (nest' $ pp t)
                          $$ 
                          pp "else"
                          $$
                          (nest' $ pp e)

nkid :: NKPolicy
nkid   = NKFilter NKTrue

nkdrop :: NKPolicy
nkdrop = NKFilter NKFalse



type PMap = [((String, String), IM.IntMap Int)]

-- Generate all switches in the topology
genSwitches :: Refine -> PhyTopology -> [(InstanceDescr, NKPolicy)]
genSwitches r topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = concatMap (\((i,o),plinks) -> let m = IM.fromList $ map (\(l,p,_) -> (l,p)) plinks
                                                                                                   in [((i,o), m)]) links
                                                          in (descr, mkSwitch r kmap pmap)) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology

-- Generate NetKAT switch 
mkSwitch :: Refine -> KMap -> PMap -> NKPolicy
mkSwitch r kmap pmap = 
    let ?r = r in
    let ?pmap = pmap in
    let polPorts = concatMap (\((pname, _), m) -> let ?role = getRole r pname in
                                                  let ?c = CtxRole ?role in
                                                  let pkey = last $ roleKeys ?role in
                                                  let TUInt _ pwidth = typ' ?r ?c pkey in
                                                  map (\(lport, pport) -> (pport, evalState (mkStatement True $ roleBody ?role) 
                                                                                            $ M.insert (name pkey) (EInt nopos pwidth $ fromIntegral lport) kmap))
                                                      $ IM.toList m)
                             pmap
    in foldr (\(port, pol) accPol -> NKITE (NKTest $ NKLocation port) pol accPol) nkdrop polPorts

mkStatement :: (?r::Refine, ?c::ECtx, ?role::Role, ?pmap::PMap) => Bool -> Statement -> State KMap NKPolicy
mkStatement final (SSeq _ l r)    = (liftM2 NKSeq) (mkStatement False l) (mkStatement final r)
mkStatement final (SPar _ l r)    = (liftM2 NKUnion) (mkStatement final l) (mkStatement final r)
mkStatement final (SITE _ c t me) = do
    kmap <- get
    let c' = evalExpr kmap c
    t' <- mkStatement final t
    e' <- maybe (return $ if' final nkdrop nkid) (mkStatement final) me
    case c' of
         EBool _ True  -> return t'
         EBool _ False -> return e'
         _             -> return $ NKITE (mkCond c') t' e'
mkStatement True  (STest _ _)     = return nkdrop
mkStatement False (STest _ c)     = do
    kmap <- get
    let c' = evalExpr kmap c
    return $ NKFilter (mkCond c')
mkStatement True  (SSet _ _ _)    = return nkdrop
mkStatement False (SSet _ l r)    = do
    kmap <- get
    case evalExpr kmap r of
         ECond _ cs d -> mkStatement False $ foldr (\(c,v) s -> SITE nopos c (SSet nopos l v) $ Just s) (SSet nopos l d) cs
         r'           -> let rscalars = exprScalars ?r ?c r'
                             lscalars = exprScalars ?r ?c l
                             stats = map (\(le, re) -> NKMod $ mkHeaderVal le re) $ zip lscalars rscalars
                         in return $ foldr (\s ss -> NKSeq s ss) (last stats) (init stats)
mkStatement _ (SSend _ dst)       = do
    kmap <- get
    let ELocation _ n ks = evalExpr kmap dst
    let EInt _ _ lpnum = last ks
    let ppnum = (snd $ fromJust $ find ((==n) . snd . fst) ?pmap) IM.! (fromIntegral lpnum)
    return $ NKMod $ NKLocation ppnum
mkStatement _     (SSendND _ _ _) = error "NetKAT.mkStatement SSendND"
mkStatement _     (SHavoc _ _)    = error "NetKAT.mkStatement SHavoc"
mkStatement _     (SAssume _ _)   = error "NetKAT.mkStatement SAssume"
mkStatement True  (SLet _ _ _ _)  = return nkdrop
mkStatement False (SLet _ _ n v)  = do
    kmap <- get
    let v' = evalExpr kmap v
    put $ M.insert n v' kmap
    return nkid
mkStatement _     (SFork _ _ c _) | exprRefersToPkt c = error "NetKAT.mkStatement: fork condition refers to packet"
mkStatement final st@(SFork _ vs c b) = do
    kmap <- get
    let c' = evalExpr kmap c
        sols = enumSolutions ?role [c']
    branches <- mapM (\sol -> let ?kmap = foldl' (\km (var, val) -> M.insert var val km) kmap $ M.toList sol in 
                              let freevars = (map name vs) \\ (map fst $ M.toList ?kmap) in
                              if null freevars
                                 then mkStatement final b
                                 else error $ "NetKAT.mkStatement " ++ show st ++ ". Unconstrained fork variables: " ++ show freevars) sols
    case branches of
         []   -> return nkdrop
         [br] -> return br
         _    -> return $ foldl' NKUnion (head branches) (tail branches)

mkCond :: (?r::Refine, ?c::ECtx, ?role::Role) => Expr -> NKPred
mkCond   (EBool _ True)     = NKTrue
mkCond   (EBool _ False)    = NKFalse
mkCond   (EBinOp _ And l r) = NKAnd (mkCond l) (mkCond r)
mkCond   (EBinOp _ Or l r)  = NKOr  (mkCond l) (mkCond r)
mkCond e@(EBinOp _ Eq l r)  = case (l,r) of
                                   (EInt _ _ _, _) -> NKTest $ mkHeaderVal r l
                                   (_, EInt _ _ _) -> NKTest $ mkHeaderVal l r
                                   _               -> error $ "NetKAT.mkCond " ++ show e
mkCond   (EUnOp _ Not c)    = NKNeg (mkCond c)
mkCond e                    = error $ "NetKAT.mkCond " ++ show e


nkHeaders :: [(Expr, Expr -> NKHeaderVal)]
nkHeaders = [ (ethSrc,  (\(EInt _ _ v) -> NKEthSrc v))
            , (ethDst,  (\(EInt _ _ v) -> NKEthDst v))
            , (vid,     (\(EInt _ _ v) -> NKVlan $ fromIntegral v))
            , (ip4Src,  (\(EInt _ _ v) -> NKIP4Src (fromIntegral v) 32))
            , (ip4Dst,  (\(EInt _ _ v) -> NKIP4Dst (fromIntegral v) 32))
            , (ip4Prot, (\(EInt _ _ v) -> NKIPProto $ fromIntegral v))]
   where pkt = EPacket nopos
         field e f = EField nopos e f
         eth     = field pkt  "eth"
         ip4     = field pkt  "ip4"
         ethSrc  = field eth  "srcAddr"
         ethDst  = field eth  "dstAddr"
         ip4Src  = field ip4  "src"
         ip4Dst  = field ip4  "dst"
         ip4Prot = field ip4  "protocol"
         vlan    = field pkt  "vlan"
         vid     = field vlan "vid"


mkHeaderVal :: Expr -> Expr -> NKHeaderVal
mkHeaderVal h v = case lookup h nkHeaders of
                       Just f   -> f v
                       Nothing  -> error $ "NetKAT.mkHeaderVal: header " ++ show h ++ " not supported"
