{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

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

-- Register allocation for intermediate representation

{-# LANGUAGE ImplicitParams, RecordWildCards, OverloadedStrings, TupleSections, FlexibleContexts #-}

module IR.Registers ( RegisterFile(..)
                    , Register(..)
                    , RegField(..)
                    , RegName
                    , RegFieldName
                    , allocVarsToRegisters) where

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import Data.List
import Data.Maybe
import GHC.Exts
--import Debug.Trace

import Util
import IR.IR
import qualified SMT.SMTSolver as S
import qualified SMT.SMTLib2   as S
import SMT.SMTSolver ((#==), (#<), (#<=), (#>=), (#&&), (#||), (#=>), (#+))

data RegisterFile = RegisterFile [Register]

type RegName   = String
type RegFieldName = String

data Register = Register { regName   :: RegName
                         , regSize   :: Int
                         , regFields :: [RegField]
                         }

data RegField = RegField { fieldName   :: RegFieldName
                         , fieldSize   :: Int
                         , fieldOffset :: Int
                         }

vRegName :: VarName -> String
vRegName v = v ++ "#reg"

vOffName :: VarName -> String
vOffName v = v ++ "#off"

vReg :: VarName -> S.Expr
vReg v = S.EVar $ vRegName v

vOff :: VarName -> S.Expr
vOff v = S.EVar $ vOffName v

allocRegisters :: (MonadError String me) => Pipeline -> RegisterFile -> me (M.Map VarName (Int, Int))
allocRegisters pl@Pipeline{..} (RegisterFile regs) = 
    case mmodel of
         Nothing       -> throwError "Register allocation failed (SMT solver terminated without producing an answer)"
         Just Nothing  -> throwError er
         _             -> return allocation
    where 
    -- for each location, determine the set of variables live at this location
    livesets = execState (cfgMapCtxM g f h plCFG) []
        where g nd node  = do modify $ ((ctxLiveVars pl $ CtxNode nd): )
                              return node
              f ctx      = do modify $ ((ctxLiveVars pl ctx):)
                              return $ Just $ ctxAction plCFG ctx
              h ctx      = do modify $ ((ctxLiveVars pl ctx):)
                              return $ bbNext $ ctxGetBB plCFG ctx
    -- pairs of simultaneously live variables
    pairs = nub $ concatMap (\vs -> filter (\(v1,v2) -> v1 > v2) -- remove symmetric and redundant pairs
                                    $ (,) <$> vs <*> vs) livesets
    
    -- SMT encoding:
    -- encoding variables: for each variable, register and offset 
    smtvars = concatMap (\(v,_) -> [S.Var (vRegName v) S.TInt, S.Var (vOffName v) S.TInt]) $ M.toList plVars
    int = S.EInt . fromIntegral
    -- hard constraints: + register index within range
    --                   + variables are within register boundaries
    --                   + variables don't overlap

    regValid = map (\(v,_) -> (vReg v #>= int 0) #&& (vReg v #< (int $ length regs))) 
                   $ M.toList plVars
    offValid = map (\(v,t) -> let w = typeWidth t in
                              (vOff v #>= int 0) #&&
                              (S.conj $ mapIdx (\Register{..} i -> 
                                                   (vReg v #== int i) #=> 
                                                   ((vOff v #+ int w) #<= int regSize))
                                               $ regs))
                   $ M.toList plVars

    noOverlap = map (\(v1, v2) -> let w1 = typeWidth $ plVars M.! v1
                                      w2 = typeWidth $ plVars M.! v2
                                  in (vReg v1 #== vReg v2) #=>
                                     ((vOff v1 #>= (vOff v2 #+ int w2)) #|| 
                                      (vOff v2 #>= (vOff v1 #+ int w1))))
                    $ pairs
    -- soft constraints: 
    -- + for each variable and each field that is big enough to fit this variable, 
    --   penalize the variable if it overlaps with the field, but is
    --   not fully contained in it
    fieldOverlap = concatMap (\(v,t) -> let w = typeWidth t in
                                        concat 
                                        $ mapIdx (\Register{..} i -> 
                                                   map (\RegField{..} -> 
                                                         (vReg v #== int i) #=> 
                                                         (((vOff v #>= int fieldOffset) #|| (vOff v #<= (int $ fieldOffset - w))) #&&
                                                          ((vOff v #>= (int $ fieldOffset + fieldSize)) #|| (vOff v #<= (int $ fieldOffset + fieldSize - w)))))
                                                       $ filter ((>= w) . fieldSize) regFields)
                                                 $ regs)
                   $ M.toList plVars
    hard = regValid ++ offValid ++ noOverlap
    q = S.SMTQuery { smtStructs = []
                   , smtVars    = smtvars
                   , smtFuncs   = []
                   , smtHard    = hard
                   , smtSoft    = map (,1) fieldOverlap
                   }
    solver = S.newSMTLib2Solver S.z3Config
    mmodel = (S.smtGetModel solver) q
    mcore = (S.smtGetCore solver) q{S.smtSoft=[]}
    Just (Just asn) = mmodel
    er = case mcore of
              Just (Just core) -> "Register allocation failed. Unsatisfiable core: " ++ (intercalate ", " $ map (show . (hard !!)) core)
              _                -> "Register allocations failed and no unsatisfiable core has been produced"
    allocation = M.mapWithKey (\v _ -> let S.EInt reg = asn M.! vRegName v
                                           S.EInt off = asn M.! vOffName v
                                       in (fromInteger reg, fromInteger off)) plVars


allocVarsToRegisters :: (MonadError String me) => Pipeline -> RegisterFile -> me Pipeline
allocVarsToRegisters pl rf@(RegisterFile regs) = do
    allocation <- allocRegisters pl rf
    let -- find the smallest field that covers the range
        field :: (Int, Int, Int) -> Either (Register, Int) (RegField, Int)
        field (rid, off, w) | null fits = Left  (r, off)
                            | otherwise = Right (fit, off - fieldOffset fit)
            where r@Register{..} = regs !! rid
                  fits = sortWith fieldSize 
                         $ filter (\f -> fieldOffset f <= off && fieldOffset f + fieldSize f >= off + w) regFields
                  fit = head fits
    let var2field :: VarName -> Either (Register, Int) (RegField, Int)
        var2field v = field (rid, off, w)
            where w = typeWidth $ plVars pl M.! v
                  (rid, off) = allocation M.! v
    let var2fname :: VarName -> VarName
        var2fname v = case var2field v of
                           Left  (Register{..}, _) -> regName
                           Right (RegField{..}, _) -> fieldName
    let vars2fnames :: [VarName] -> [VarName]
        vars2fnames vs = nub $ map var2fname vs
    let mkvars :: Vars -> Vars
        mkvars vars = foldl' (\vs v -> if isNothing $ M.lookup v allocation
                                          then M.insert v (vars M.! v) vs
                                          else case var2field v of
                                                    Left (Register{..}, _)  -> M.insert regName (TBit regSize) vs
                                                    Right (RegField{..}, _) -> M.insert fieldName (TBit fieldSize) vs) M.empty 
                             $ M.keys vars
    let rename :: Expr -> Expr
        rename = exprMap rename'
        rename' :: Expr -> Expr
        rename' (EVar v t) | isNothing (M.lookup v allocation) = EVar v t
                           | otherwise                         = e
            where (rid, off) = allocation M.! v
                  w = typeWidth t
                  e = case field (rid, off, w) of
                           Left (Register{..}, off')  -> if regSize == w
                                                            then EVar regName $ TBit regSize
                                                            else ESlice (EVar regName $ TBit regSize) (off' + w - 1) off'
                           Right (RegField{..}, off') -> if fieldSize == w
                                                            then EVar fieldName $ TBit fieldSize
                                                            else ESlice (EVar fieldName $ TBit fieldSize) (off' + w - 1) off'
        rename' (ESlice (ESlice (EVar v t) _ l) h' l') = ESlice (EVar v t) (l + h') (l + l')
        rename' e = e
    let g :: NodeId -> Node -> Node
        g _  node = case node of
                         Fork t vs pl' b       -> let cfg = plCFG pl' in
                                                  Fork t (vars2fnames vs) (pl'{plVars = mkvars $ plVars pl', plCFG = cfgMapCtx g (f cfg) (h cfg) cfg}) b
                         Lookup t vs pl' th el -> let cfg = plCFG pl' in
                                                  Lookup t (vars2fnames vs) (pl'{plVars = mkvars $ plVars pl', plCFG = cfgMapCtx g (f cfg) (h cfg) cfg}) th el
                         Cond cs               -> Cond $ map (mapFst rename) cs
                         Par bs                -> Par bs
        f :: CFG -> CFGCtx -> Maybe Action
        f cfg ctx = case ctxAction cfg ctx of
                         ASet    l r  -> Just $ ASet (rename l) (rename r)
                         APut    t as -> Just $ APut t (map rename as)
                         ADelete t c  -> Just $ ADelete t (rename c)
        h :: CFG -> CFGCtx -> Next
        h cfg ctx = case bbNext $ ctxGetBB cfg ctx of
                         Send x -> Send $ rename x
                         n      -> n
    let cfg' = cfgMapCtx g (f $ plCFG pl) (h $ plCFG pl) $ plCFG pl
    return {-$ trace ("register allocation:\n" ++ 
                    (concatMap (\(v,t) -> v ++ ": " ++ show t ++ " -> " ++ show (rename $ EVar v) ++ "\n") $ M.toList $ plVars pl))-}
           $ pl{plVars = mkvars $ plVars pl, plCFG = cfg'}
