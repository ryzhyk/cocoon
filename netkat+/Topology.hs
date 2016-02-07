{-# LANGUAGE ImplicitParams #-}

-- Managing physical network topology induced by a NetKAT+ spec

module Topology () where

import qualified Data.Map as M

import Eval
import Syntax
import Name
import NS
import Pos
import qualified SMT.SMTSolver as SMT
import qualified SMT.SMTLib2   as SMT

-- Multidimensional array of switch instances.  Each dimension corresponds to a 
-- key.  Innermost elements enumerate ports of an instance.
newtype InstanceMap = InstanceMap (Either [(Expr, InstanceMap)] PortMap)

-- Input-output port pair; a list of port indices and remote ports they are 
-- connected to.
type PortMap = [((String, String), [(Int, Maybe InstanceDescr)])]

-- Role instance descriptor
data InstanceDescr = InstanceDescr String [Expr] 

type Topology = [(String, InstanceMap)]

generateTopology :: Refine -> FMap -> Topology
generateTopology r fmap = let ?r = r in 
                          let ?fmap = fmap in
                          map (\s -> (name s, mkSwitchInstMap s)) $ refineSwitches r

mkSwitchInstMap :: (?r::Refine, ?fmap::FMap) => Switch -> InstanceMap
mkSwitchInstMap sw = mkSwitchInstMap' sw M.empty (roleKeys $ getRole ?r (swName sw))

mkSwitchInstMap' :: (?r::Refine, ?fmap::FMap) => Switch -> KMap -> [Field] -> InstanceMap
mkSwitchInstMap' sw kmap []     = InstanceMap $ Right $ mkSwitchPortMap sw kmap
mkSwitchInstMap' sw kmap (f:fs) = InstanceMap $ Left $ map (\e -> (e, mkSwitchInstMap' sw (M.insert (name f) e kmap) fs)) $ solveFor swrole fConstr (name f)
    -- Equation to compute possible values of f from:
    where fConstr = EBinOp nopos And (roleKeyRange swrole)  keyVals
          swrole = getRole ?r $ swName sw
          keyVals = conj $ map (\(k,v) -> EBinOp nopos Eq (EKey nopos k) v) $ M.toList kmap

mkSwitchPortMap :: (?r::Refine, ?fmap::FMap) => Switch -> KMap -> PortMap
mkSwitchPortMap sw kmap = map (\ports -> (ports, mkSwitchPortMap' sw kmap ports)) $ swPorts sw

mkSwitchPortMap' :: (?r::Refine, ?fmap::FMap) => Switch -> KMap -> (String, String) -> [(Int, Maybe InstanceDescr)]
mkSwitchPortMap' sw kmap (i,o) = map (\e@(EInt _ pnum) -> (fromInteger pnum, mkLink outrole (M.insert portKey e kmap))) 
                                     $ solveFor inrole pConstr portKey 
    -- Equation to compute possible values of port index (last key of the port role):
    where pConstr = EBinOp nopos And (roleKeyRange inrole) keyVals
          inrole = getRole ?r i
          outrole = getRole ?r o
          portKey = name $ last $ roleKeys inrole
          keyVals = conj $ map (\(k,v) -> EBinOp nopos Eq (EKey nopos k) v) $ M.toList kmap

-- Compute remote port role is connected to.  Role must be an output port of a switch.
mkLink :: (?r::Refine, ?fmap::FMap) => Role -> KMap -> Maybe InstanceDescr
mkLink role kmap = let ?kmap = kmap in 
                   let ?role = role in
                   case evalPortStatement (roleBody role) of
                        SSend _ (ELocation _ n ks) -> Just $ InstanceDescr n ks
                        STest _ (EBool _ False)    -> Nothing
                        _                          -> error $ "mkLink: output port " ++ name role ++ " does not evaluate to a constant"

-- Evaluate output port body.  Assume that it can only consist of 
-- conditions and send statements, i.e., it cannot modify or clone packets.
evalPortStatement :: (?r::Refine, ?role::Role, ?fmap::FMap, ?kmap::KMap) => Statement -> Statement
evalPortStatement (SSend _ e)    = SSend nopos $ evalExpr e
evalPortStatement (SITE _ c t e) = case evalExpr c of
                                        EBool _ True  -> evalPortStatement t
                                        EBool _ False -> evalPortStatement e
                                        _             -> error "Topology.evalPortStatement: condition does not evaluate to a constant"
evalPortStatement (SSeq  _ s1 s2) = case evalPortStatement s1 of
                                         STest _ (EBool _ True)        -> evalPortStatement s2
                                         s1'@(STest _ (EBool _ False)) -> s1'
                                         _                             -> error "Topology.evalPortStatement: statement does not evaluate to a constant"
evalPortStatement (STest _ cond) = STest nopos $ evalExpr cond

               -- | SPar  {statPos :: Pos, statLeft :: Statement, statRight :: Statement}
               -- | SSet  {statPos :: Pos, statLVal :: Expr, statRVal :: Expr}

-- Solve equation e for variable var; returns all satisfying assignments.
solveFor :: (?r::Refine, ?fmap::FMap) => Role -> Expr -> String -> [Expr]
solveFor role e var = map exprFromSMT $ SMT.allSolutions solver (expr2SMTQuery role e) var
    where solver = SMT.newSMTLib2Solver SMT.z3Config

expr2SMTQuery :: (?r::Refine) => Role -> Expr -> SMT.SMTQuery
expr2SMTQuery = undefined

exprFromSMT :: SMT.Expr -> Expr
exprFromSMT = undefined
