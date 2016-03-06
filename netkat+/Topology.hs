{-# LANGUAGE ImplicitParams, RecordWildCards #-}

-- Managing physical network topology induced by a NetKAT+ spec

module Topology ( Topology
                , InstanceDescr(..)
                , PortInstDescr(..)
                , InstanceMap(..)
                , instMapFlatten
                , PortLinks
                , nodeFromPort
                , portFromNode
                , phyPortNum
                , generateTopology) where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Tuple.Select
import Control.Monad.State

import Eval
import Syntax
import Name
import NS
import Pos
import Type
import Expr
import qualified SMT.SMTSolver as SMT
import qualified SMT.SMTLib2   as SMT


-- Multidimensional array of switch instances.  Each dimension corresponds to a 
-- key.  Innermost elements enumerate ports of an instance.
newtype InstanceMap = InstanceMap (Either [(Expr, InstanceMap)] PortLinks)

instMapFlatten :: Node -> InstanceMap -> [(InstanceDescr, PortLinks)]
instMapFlatten node (InstanceMap (Left insts))  = concatMap (\(k, imap) -> map (\(InstanceDescr n keys, links) -> (InstanceDescr n (k:keys), links)) $ instMapFlatten node imap) insts
instMapFlatten node (InstanceMap (Right links)) = [(InstanceDescr (name node) [], links)]

-- ((input_port_name, output_port_name), (first_physical_portnum, last_physical_portnum), (logical_out_port_index -> remote_port))
type PortLinks = [((String, String), (Int, Int), [(Int, Maybe PortInstDescr)])]

-- Role instance descriptor
data InstanceDescr = InstanceDescr {idescNode::String, idescKeys::[Expr]} deriving (Eq, Show)
data PortInstDescr = PortInstDescr {pdescPort::String, pdescKeys::[Expr]} deriving (Eq, Show)

type Topology = [(Node, InstanceMap)]

getInstPortMap :: Topology -> InstanceDescr -> PortLinks
getInstPortMap t (InstanceDescr ndname keys) = getInstPortMap' (snd $ fromJust $ find ((==ndname) . name . fst) t) keys

getInstPortMap' :: InstanceMap -> [Expr] -> PortLinks
getInstPortMap' (InstanceMap (Left mp))     (k:ks) = getInstPortMap' (fromJust $ lookup k mp) ks
getInstPortMap' (InstanceMap (Right links)) []     = links
getInstPortMap' _ _                                = error "Topology.getInstPortMap': unexpected input"

phyPortNum :: Topology -> InstanceDescr -> String -> Int -> Int
phyPortNum t inst pname pnum = base + pnum
    where plinks = getInstPortMap t inst
          (_, (base, _), _) = fromJust $ find ((\(i,o) -> i == pname || o == pname) . sel1) plinks

nodeFromPort :: Refine -> PortInstDescr -> InstanceDescr
nodeFromPort r (PortInstDescr pname keys) = InstanceDescr noderole $ init keys
    where noderole = name $ fromJust $ find (isJust . find (\(i,o) -> i == pname || o == pname) . nodePorts) $ refineNodes r

portFromNode :: Refine -> InstanceDescr -> String -> Int -> PortInstDescr
portFromNode r (InstanceDescr _ ks) pname pnum = PortInstDescr pname (ks++[EInt nopos w $ fromIntegral pnum])
    where prole = getRole r pname
          TUInt _ w = typ' r (CtxRole prole) $ last $ roleKeys prole

generateTopology :: Refine -> Topology
generateTopology r = let ?r = r in 
                     map (\n -> (n, mkNodeInstMap n)) $ refineNodes r

mkNodeInstMap :: (?r::Refine) => Node -> InstanceMap
mkNodeInstMap nd = mkNodeInstMap' nd M.empty (roleKeys $ getRole ?r (name nd))

mkNodeInstMap' :: (?r::Refine) => Node -> KMap -> [Field] -> InstanceMap
mkNodeInstMap' nd kmap []     = InstanceMap $ Right $ mkNodePortLinks nd kmap
mkNodeInstMap' nd kmap (f:fs) = InstanceMap $ Left $ map (\e -> (e, mkNodeInstMap' nd (M.insert (name f) e kmap) fs)) $ solveFor ndrole fConstr (name f)
    -- Equation to compute possible values of f from:
    where fConstr = (roleKeyRange ndrole):keyVals
          ndrole = getRole ?r $ nodeName nd
          keyVals = map (\(k,v) -> EBinOp nopos Eq (EVar nopos k) v) $ M.toList kmap

mkNodePortLinks :: (?r::Refine) => Node -> KMap -> PortLinks
mkNodePortLinks nd kmap = evalState (mapM (\ports -> do let links = mkNodePortLinks' kmap ports 
                                                            lastport = maximum $ map fst links
                                                        base <- get
                                                        put $ base + lastport + 1
                                                        return (ports, (base, base+lastport), links)) $ nodePorts nd)
                                    0

mkNodePortLinks' :: (?r::Refine) => KMap -> (String, String) -> [(Int, Maybe PortInstDescr)]
mkNodePortLinks' kmap (i,o) = map (\e@(EInt _ _ pnum) -> (fromInteger pnum, mkLink outrole (M.insert portKey e kmap))) 
                                  $ solveFor inrole pConstr portKey 
    -- Equation to compute possible values of port index (last key of the port role):
    where pConstr = (roleKeyRange inrole):keyVals
          inrole = getRole ?r i
          outrole = getRole ?r o
          portKey = name $ last $ roleKeys inrole
          keyVals = map (\(k,v) -> EBinOp nopos Eq (EVar nopos k) v) $ M.toList kmap

-- Compute remote port role is connected to.  Role must be an output port of a switch.
mkLink :: (?r::Refine) => Role -> KMap -> Maybe PortInstDescr
mkLink role kmap = let ?kmap = kmap in 
                   let ?role = role in
                   case evalPortStatement (roleBody role) of
                        SSend _ (ELocation _ n ks) -> Just $ PortInstDescr n ks
                        STest _ (EBool _ False)    -> Nothing
                        _                          -> error $ "mkLink: output port " ++ name role ++ " does not evaluate to a constant"

-- Evaluate output port body.  Assume that it can only consist of 
-- conditions and send statements, i.e., it cannot modify or clone packets.
evalPortStatement :: (?r::Refine, ?role::Role, ?kmap::KMap) => Statement -> Statement
evalPortStatement (SSend _ e)    = SSend nopos $ evalExpr e
evalPortStatement (SITE _ c t e) = case evalExpr c of
                                        EBool _ True  -> evalPortStatement t
                                        EBool _ False -> case e of
                                                              Nothing -> STest nopos (EBool nopos False)
                                                              Just e' -> evalPortStatement e'
                                        _             -> error "Topology.evalPortStatement: condition does not evaluate to a constant"
evalPortStatement (SSeq  _ s1 s2) = case evalPortStatement s1 of
                                         STest _ (EBool _ True)        -> evalPortStatement s2
                                         s1'@(STest _ (EBool _ False)) -> s1'
                                         _                             -> error "Topology.evalPortStatement: statement does not evaluate to a constant"
evalPortStatement (STest _ cond) = STest nopos $ evalExpr cond
evalPortStatement s              = error $ "Topology.evalPortStatement " ++ show s

               -- | SPar  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               -- | SSet  {statPos :: Pos, statLVal :: Expr, statRVal :: Expr}

-- Solve equation e for variable var; returns all satisfying assignments.
solveFor :: (?r::Refine) => Role -> [Expr] -> String -> [Expr]
solveFor role es var = map exprFromSMT $ SMT.allSolutions solver (exprs2SMTQuery role es) var
    where solver = SMT.newSMTLib2Solver SMT.z3Config

exprs2SMTQuery :: (?r::Refine) => Role -> [Expr] -> SMT.SMTQuery
exprs2SMTQuery role es = let ?role = role in
                         let es' = map expr2SMT es
                             smtvs = (SMT.Var pktVar (typ2SMT $ typ'' ?r (CtxRole role) $ TUser nopos packetTypeName)) : 
                                     (map (\k -> SMT.Var (name k) (typ2SMT $ typ'' ?r (CtxRole role) k)) $ roleKeys role)
                             structs = mapMaybe (\d -> case tdefType d of
                                                            TStruct _ fs -> Just $ SMT.Struct (tdefName d) $ map (\f -> (name f, typ2SMT $ typ'' ?r (CtxRole ?role) f)) fs
                                                            _            -> Nothing) 
                                                $ refineTypes ?r
                             smtfuncs = map (func2SMT . getFunc ?r) $ nub $ concatMap exprFuncs es
                         in SMT.SMTQuery structs smtvs smtfuncs es'

func2SMT :: (?r::Refine) => Function -> SMT.Function
func2SMT f@Function{..} = SMT.Function funcName 
                                       (map (\a -> (name a, typ2SMT $ typ'' ?r (CtxFunc f) a)) funcArgs) 
                                       (typ2SMT $ typ'' ?r (CtxFunc f) funcType)
                                       (expr2SMT $ fromJust funcDef)

typ2SMT :: (?r::Refine) => Type -> SMT.Type
typ2SMT (TBool _)     = SMT.TBool
typ2SMT (TUInt _ w)   = SMT.TUInt w
typ2SMT (TUser _ n)   = SMT.TStruct n
typ2SMT (TLocation _) = SMT.TUInt 32 -- TODO: properly encode location to SMT as ADT with multiple constructors
typ2SMT t             = error $ "Topology.typ2SMT " ++ show t

expr2SMT :: (?r::Refine) => Expr -> SMT.Expr
expr2SMT (EVar _ k)          = SMT.EVar k
expr2SMT (EPacket _)         = SMT.EVar pktVar
expr2SMT (EApply _ f as)     = SMT.EApply f $ map expr2SMT as
expr2SMT (EField _ s f)      = SMT.EField (expr2SMT s) f
expr2SMT (EBool _ b)         = SMT.EBool b
expr2SMT (EInt _ w i)        = SMT.EInt w i
expr2SMT (EStruct _ s fs)    = SMT.EStruct s $ map expr2SMT fs
expr2SMT (EBinOp _ op e1 e2) = SMT.EBinOp op (expr2SMT e1) (expr2SMT e2)
expr2SMT (EUnOp _ op e1)     = SMT.EUnOp op (expr2SMT e1)
expr2SMT (ECond _ cs d)      = SMT.ECond (map (\(c,v) -> (expr2SMT c, expr2SMT v)) cs) (expr2SMT d)

-- Convert constant SMT expression to Expr
exprFromSMT :: SMT.Expr -> Expr
exprFromSMT (SMT.EBool b)      = EBool nopos b
exprFromSMT (SMT.EInt w i)     = EInt nopos w i
exprFromSMT (SMT.EStruct n fs) = EStruct nopos n $ map exprFromSMT fs
exprFromSMT e                  = error $ "Topology.exprFromSMT " ++ show e
