{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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
{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Eval ( KMap
            , evalExpr) where

import qualified Data.Map as M
import Data.Maybe
import Data.Bits 
import Data.List
import Control.Monad.State.Strict

import qualified SMT           as SMT
import qualified SMT.SMTSolver as SMT
import qualified SMT.Datalog   as DL
import Syntax
import Type
import Name
import NS
import Util
import Pos

-- Key map: maps keys into their values
type KMap = M.Map String Expr

evalExpr :: Refine -> ECtx -> KMap -> DL.Session -> Expr -> IO (Expr, KMap)
evalExpr r ctx kmap dl e = let ?dl = dl      
                               ?r = r 
                           in runStateT (evalExpr' ctx e) kmap

evalExpr' :: (?r::Refine, ?dl::DL.Session) => ECtx -> Expr -> StateT KMap IO Expr
evalExpr' ctx (E e) = evalExpr'' ctx e

evalExpr'' :: (?r::Refine, ?dl::DL.Session) => ECtx -> ENode -> StateT KMap IO Expr
evalExpr'' ctx e = do
    case e of
        EVar _ v        -> (liftM (M.! v)) get
        EApply _ f as   -> do let fun = getFunc ?r f
                              kmap' <- liftM M.fromList 
                                       $ liftM (zip (map name $ funcArgs fun)) 
                                       $ mapIdxM (\a i -> evalExpr' (CtxApply e ctx i) a)as
                              kmap <- get
                              put kmap'
                              v <- evalExpr' (CtxFunc fun ctx) (fromJust $ funcDef fun)
                              put kmap
                              return v
        EField _ s f    -> do s' <- evalExpr' (CtxField e ctx) s
                              case enode s' of
                                   EStruct _ c fs -> do let cons = getConstructor ?r c
                                                            fidx = maybe (error $ "field " ++ f ++ " does not exist in expression " ++ show e ++ " at " ++ show (pos e)) id
                                                                         $ findIndex ((==f) . name) $ consArgs cons
                                                        return $ fs !! fidx
                                   _              -> return $ eField s' f
        EBool{}         -> return $ E e
        EInt{}          -> return $ case exprType ?r ctx (E e) of
                                         TInt _   -> E e
                                         TBit _ w -> eBit w (exprIVal e)
                                         _        -> error $ "EVal.evalExpr EInt " ++ show e
        EString{}       -> return $ E e
        EBit{}          -> return $ E e
        EStruct _ c fs  -> liftM (eStruct c) $ mapIdxM (\f i -> evalExpr' (CtxStruct e ctx i) f) fs
        ETuple _ fs     -> liftM eTuple $ mapIdxM (\f i -> evalExpr' (CtxTuple e ctx i) f) fs
        ESlice _ op h l -> do op' <- evalExpr' (CtxSlice e ctx) op
                              return $ case enode op' of
                                            EBit _ w v -> eBit w $ bitSlice v h l
                                            _          -> eSlice op' h l
        EMatch _ m cs   -> do m' <- evalExpr' (CtxMatchExpr e ctx) m
                              case findIndex (match m' . fst) cs of
                                   Just i      -> do let (c, v) = cs !! i
                                                     kmap <- get
                                                     assignTemplate (CtxMatchPat e ctx i) c m'
                                                     v' <- evalExpr' (CtxMatchVal e ctx i) v
                                                     put kmap
                                                     return v'
                                   Nothing     -> error $ "No match found in\n" ++ show e ++ 
                                                          "\nwhere match expression evaluates to " ++ show m'
        EVarDecl _ v    -> do let v' = error $ "variable " ++ v ++ " has undefined value"
                              modify $ M.insert v v'
                              return v'
        ESeq _ e1 e2    -> do _ <- evalExpr' (CtxSeq1 e ctx) e1
                              evalExpr' (CtxSeq2 e ctx) e2
        EITE _ c t el   -> do E c' <- evalExpr' (CtxITEIf e ctx) c
                              case c' of
                                   EBool _ True  -> evalExpr' (CtxITEThen e ctx) t
                                   EBool _ False -> maybe (return $ eTuple [])
                                                          (evalExpr' (CtxITEElse e ctx))
                                                          el
                                   _             -> error $ "Condition does not evaluate to a constant in\n" ++ show e
        ESet _ l r      -> do r' <- evalExpr' (CtxSetR e ctx) r
                              assignTemplate (CtxSetL e ctx) l r'
                              return $ eTuple []
        EBinOp _ op l r -> do l' <- evalExpr' (CtxBinOpL e ctx) l
                              r' <- evalExpr' (CtxBinOpR e ctx) r
                              return $ evalBinOp $ eBinOp op l' r'
        EUnOp  _ Not a -> do E a' <- evalExpr' (CtxUnOp e ctx) a
                             return $ case a' of
                                           EBool _ v -> eBool $ not v
                                           _         -> eNot $ E a'
        EFor _ v t c b -> do let rel = getRelation ?r t
                             rows <- lift $ (liftM $ map (assignment2Row rel)) $ DL.enumRelation ?dl t
                             mapM_ (\row -> do kmap <- get
                                               modify $ M.insert v row
                                               E c' <- evalExpr' (CtxForCond e ctx) c 
                                               case c' of
                                                    EBool{} -> return ()
                                                    _       -> error $ "Query condition does not evaluate to a constant in\n" ++ show e
                                               when (exprBVal c') $ do _ <- evalExpr' (CtxForBody e ctx) b
                                                                       return ()
                                               put kmap)
                                   rows
                             return $ eTuple []
        EWith _ v t c b d -> do let rel = getRelation ?r t
                                rows <- lift $ (liftM $ map (assignment2Row rel)) $ DL.enumRelation ?dl t
                                rows' <- filterM (\row -> do kmap <- get
                                                             modify $ M.insert v row
                                                             E c' <- evalExpr' (CtxWithCond e ctx) c 
                                                             case c' of
                                                                  EBool{} -> return ()
                                                                  _       -> error $ "Query condition does not evaluate to a constant in\n" ++ show e
                                                             put kmap
                                                             return $ exprBVal c') 
                                                 rows
                                case rows' of
                                     [row] -> do kmap <- get
                                                 modify $ M.insert v row
                                                 res <- evalExpr' (CtxWithBody e ctx) b
                                                 put kmap
                                                 return res
                                     []    -> maybe (error $ "query returned no rows in\n" ++ show e)
                                                    (\d' -> evalExpr' (CtxWithDef e ctx) d')
                                                    d
                                     _     -> error $ "query returned multiple rows in\n" ++ show e ++ "\n" ++
                                                      (intercalate "\n" $ map show rows') 
        ETyped _ v _        -> evalExpr' (CtxTyped e ctx) v
        _                   -> error $ "Eval.evalExpr " ++ show e

match :: Expr -> Expr -> Bool
match (E pat) (E e) = 
    case (pat, e) of
         (_,               EVar _ _)        -> True
         (ETuple _ ps,     ETuple _ es)     -> all (uncurry match) $ zip ps es
         (EStruct _ pc ps, EStruct _ pe es) -> pc == pe && (all (uncurry match) $ zip ps es)
         (_,               EVarDecl _ _)    -> True
         (_,               EPHolder _)      -> True
         (_,               ETyped _ e' _)   -> match (E pat) e'
         _                                  -> False
 

assignTemplate :: (?r::Refine, ?dl::DL.Session) => ECtx -> Expr -> Expr -> StateT KMap IO ()
assignTemplate ctx (E l) (E r) = 
    case (l, r) of
         (EVar _ v,        _)                -> modify $ M.insert v $ E r
         (EField _ e f,    _)                -> do E (EStruct _ c fs) <- evalExpr' (CtxField l ctx) e
                                                   let cons = getConstructor ?r c
                                                   case findIndex ((== f) . name) $ consArgs cons of 
                                                        Nothing -> error $ "field " ++ f ++ " does not exist in " ++ show e ++ " at " ++ show (pos e)
                                                        Just i  -> let e' = eStruct c $ (take i fs) ++ (E r : (drop (i+1) fs)) in
                                                                   assignTemplate (CtxField l ctx) e e'
         (ETuple _ ls,     ETuple _ rs)      -> mapIdxM_ (\(l', r') i -> assignTemplate (CtxTuple l ctx i) l' r') 
                                                         $ zip ls rs 
         (EStruct _ lc ls, EStruct _ rc rs)   | lc == rc  -> mapIdxM_ (\(l',r') i -> assignTemplate (CtxStruct l ctx i) l' r') 
                                                                      $ zip ls rs
                                              | otherwise -> error $ "constructor mismatch at " ++ show (pos l) ++ 
                                                                     ": assigning value " ++ show r ++ "to " ++ show l
         (EVarDecl _ v,    _)                -> modify $ M.insert v $ E r
         (EPHolder _,      _)                -> return ()
         (ETyped _ e _,    _)                -> assignTemplate (CtxTyped l ctx) e $ E r
         _                                   -> error $ "Eval.assignTemplate " ++ show l ++ " " ++ show r

assignment2Row :: Relation -> SMT.Assignment -> Expr
assignment2Row Relation{..} asn = eStruct relName $ map (\f -> SMT.exprFromSMT $ asn M.! (name f)) relArgs

evalBinOp :: Expr -> Expr
evalBinOp e@(E (EBinOp _ op l r)) = 
    case (enode l, enode r) of
         (EBool _ v1, EBool _ v2)   -> case op of
                                            Eq   -> eBool (v1 == v2)
                                            Neq  -> eBool (v1 /= v2)
                                            And  -> eBool (v1 && v2)
                                            Or   -> eBool (v1 || v2)
                                            Impl -> eBool ((not v1) || v2)
                                            _    -> error $ "Eval.evalBinOp " ++ show e
         (EBool _ True, _)          -> case op of
                                            Eq   -> r
                                            Neq  -> eNot r
                                            And  -> r
                                            Or   -> l
                                            Impl -> r
                                            _    -> error $ "Eval.evalBinOp " ++ show e
         (EBool _ False, _)         -> case op of
                                            Eq   -> eNot r
                                            Neq  -> r
                                            And  -> l
                                            Or   -> r
                                            Impl -> eTrue
                                            _    -> error $ "Eval.evalBinOp " ++ show e
         (_, EBool _ True)          -> case op of
                                            Eq   -> l
                                            Neq  -> eNot l
                                            And  -> l
                                            Or   -> r
                                            Impl -> r
                                            _    -> error $ "Eval.evalBinOp " ++ show e
         (_, EBool _ False)          -> case op of
                                            Eq   -> eNot l
                                            Neq  -> l
                                            And  -> r
                                            Or   -> l
                                            Impl -> eNot l
                                            _    -> error $ "Eval.evalBinOp " ++ show e
         (EBit _ w1 v1, EBit _ w2 v2) -> let w = max w1 w2 in
                                         case op of
                                            Eq     -> eBool (v1 == v2)
                                            Neq    -> eBool (v1 /= v2)
                                            Lt     -> eBool (v1 < v2)
                                            Gt     -> eBool (v1 > v2)
                                            Lte    -> eBool (v1 <= v2)
                                            Gte    -> eBool (v1 >= v2)
                                            Plus   -> eBit  w ((v1 + v2) `mod` (1 `shiftL` w))
                                            Minus  -> eBit  w ((v1 - v2) `mod` (1 `shiftL` w))
                                            ShiftR -> eBit  w1 (v1 `shiftR` fromInteger(v2))
                                            ShiftL -> eBit  w1 ((v1 `shiftL` fromInteger(v2)) `mod` (1 `shiftL` w1))
                                            Concat -> eBit  (w1+w2) ((v1 `shiftL` w2) + v2)
                                            Mod    -> eBit  w1 (v1 `mod` v2)
                                            _      -> error $ "Eval.evalBinOp " ++ show e
         (EInt _ v1, EInt _ v2)      -> case op of
                                            Eq     -> eBool (v1 == v2)
                                            Neq    -> eBool (v1 /= v2)
                                            Lt     -> eBool (v1 < v2)
                                            Gt     -> eBool (v1 > v2)
                                            Lte    -> eBool (v1 <= v2)
                                            Gte    -> eBool (v1 >= v2)
                                            Plus   -> eInt (v1 + v2)
                                            Minus  -> eInt (v1 - v2)
                                            ShiftR -> eInt (v1 `shiftR` fromInteger(v2))
                                            ShiftL -> eInt (v1 `shiftL` fromInteger(v2))
                                            Mod    -> eInt (v1 `mod` v2)
                                            _      -> error $ "Eval.evalBinOp " ++ show e

         (EString _ s1, EString _ s2) -> case op of
                                            Eq     -> eBool (s1 == s2)
                                            Neq    -> eBool (s1 /= s2)
                                            _      -> error $ "Eval.evalBinOp " ++ show e
         (EStruct _ c1 fs1, EStruct _ c2 fs2) | c1 == c2 -> case op of 
                                                                 Eq  -> conj $ map (\(f1,f2) -> evalBinOp $ eBinOp Eq f1 f2) $ zip fs1 fs2
                                                                 Neq -> disj $ map (\(f1,f2) -> evalBinOp $ eBinOp Neq f1 f2) $ zip fs1 fs2
                                                                 _   -> error $ "Eval.evalBinOp " ++ show e
                                              | otherwise -> case op of
                                                                  Eq  -> eFalse
                                                                  Neq -> eTrue
                                                                  _   -> error $ "Eval.evalBinOp " ++ show e
         (ETuple _ fs1, ETuple _ fs2) -> case op of 
                                              Eq  -> conj $ map (\(f1,f2) -> evalBinOp $ eBinOp Eq f1 f2) $ zip fs1 fs2
                                              Neq -> disj $ map (\(f1,f2) -> evalBinOp $ eBinOp Neq f1 f2) $ zip fs1 fs2
                                              _   -> error $ "Eval.evalBinOp " ++ show e
         _                            -> eBinOp op l r
evalBinOp e = error $ "Eval.evalBinOp " ++ show e

--exprSimplify :: (?r::Refine, ?c::ECtx) => Expr -> Expr
--exprSimplify e = evalExpr M.empty e

-- -- Partially evaluate expression: 
-- -- Expand function definitions, substitute variable values defined in KMap
-- -- When all functions are defined and all variables are mapped into values, the result should be an expression without
-- -- function calls and with only pkt variables.
-- evalExpr  :: (?r::Refine, ?c::ECtx) => KMap -> Expr -> Expr
-- evalExpr kmap e = let ?kmap = kmap in evalExpr' e
-- 
-- evalExpr'  :: (?r::Refine, ?c::ECtx, ?kmap::KMap) => Expr -> Expr
-- evalExpr' e@(EVar _ k)                  = case M.lookup k ?kmap of
--                                               Nothing -> e
--                                               Just e' -> e'
-- evalExpr' (EApply p f as)               = 
--     case funcDef func of
--          Nothing -> EApply p f as'
--          Just e  -> let ?kmap = foldl' (\m (a,v) -> M.insert (name a) v m) M.empty $ zip (funcArgs func) as'
--                     in evalExpr' e
--     where as' = map evalExpr' as                                     
--           func = getFunc ?r f
-- evalExpr' (EBuiltin _ f as)             = (bfuncEval $ getBuiltin f) $ map evalExpr' as
-- evalExpr' (EField _ s f)                = 
--     case evalExpr' s of
--          s'@(EStruct _ _ fs) -> let (TStruct _ sfs) = typ' ?r ?c s'
--                                     fidx = fromJust $ findIndex ((== f) . name) sfs
--                                 in fs !! fidx
--          ECond _ cs d        -> ECond nopos (map (mapSnd (\v -> evalExpr' $ EField nopos v f)) cs) (evalExpr' $ EField nopos d f)
--          s'                  -> EField nopos s' f
-- evalExpr' (ELocation _ r ks)            = ELocation nopos r $ map evalExpr' ks
-- evalExpr' (EStruct _ s fs)              = EStruct nopos s $ map evalExpr' fs
-- evalExpr' e@(EBinOp _ op lhs rhs)       = 
--     let lhs' = evalExpr' lhs
--         rhs' = evalExpr' rhs
--         TUInt _ w1 = typ' ?r ?c lhs'
--         TUInt _ w2 = typ' ?r ?c rhs'
--         w = max w1 w2
--     in case (lhs', rhs') of
--             (EBool _ v1, EBool _ v2)   -> case op of
--                                                Eq   -> EBool nopos (v1 == v2)
--                                                Neq  -> EBool nopos (v1 /= v2)
--                                                And  -> EBool nopos (v1 && v2)
--                                                Or   -> EBool nopos (v1 || v2)
--                                                Impl -> EBool nopos ((not v1) || v2)
--                                                _    -> error $ "Eval.evalExpr' " ++ show e
--             (EBool _ True, _)          -> case op of
--                                                Eq   -> rhs'
--                                                Neq  -> evalExpr' $ EUnOp nopos Not rhs'
--                                                And  -> rhs'
--                                                Or   -> lhs'
--                                                Impl -> rhs'
--                                                _    -> error $ "Eval.evalExpr' " ++ show e
--             (EBool _ False, _)         -> case op of
--                                                Eq   -> evalExpr' $ EUnOp nopos Not rhs'
--                                                Neq  -> rhs'
--                                                And  -> lhs'
--                                                Or   -> rhs'
--                                                Impl -> EBool nopos True
--                                                _    -> error $ "Eval.evalExpr' " ++ show e
--             (_, EBool _ True)          -> case op of
--                                                Eq   -> lhs'
--                                                Neq  -> evalExpr' $ EUnOp nopos Not lhs'
--                                                And  -> lhs'
--                                                Or   -> rhs'
--                                                Impl -> rhs'
--                                                _    -> error $ "Eval.evalExpr' " ++ show e
--             (_, EBool _ False)          -> case op of
--                                                Eq   -> evalExpr' $ EUnOp nopos Not lhs'
--                                                Neq  -> lhs'
--                                                And  -> rhs'
--                                                Or   -> lhs'
--                                                Impl -> evalExpr' $ EUnOp nopos Not lhs'
--                                                _    -> error $ "Eval.evalExpr' " ++ show e
--             (EInt _ _ v1, EInt _ _ v2) -> case op of
--                                                Eq     -> EBool nopos (v1 == v2)
--                                                Neq    -> EBool nopos (v1 /= v2)
--                                                Lt     -> EBool nopos (v1 < v2)
--                                                Gt     -> EBool nopos (v1 > v2)
--                                                Lte    -> EBool nopos (v1 <= v2)
--                                                Gte    -> EBool nopos (v1 >= v2)
--                                                Plus   -> EInt  nopos w ((v1 + v2) `mod` (1 `shiftL` w))
--                                                Minus  -> EInt  nopos w ((v1 - v2) `mod` (1 `shiftL` w))
--                                                ShiftR -> EInt  nopos w (v1 `shiftR` fromInteger(v2))
--                                                ShiftL -> EInt  nopos w ((v1 `shiftL` fromInteger(v2)) `mod` (1 `shiftL` w))
--                                                Concat -> EInt  nopos (w1+w2) ((v1 `shiftL` w2) + v2)
--                                                Mod    -> EInt  nopos w1 (v1 `mod` v2)
--                                                _      -> error $ "Eval.evalExpr' " ++ show e
--             (EStruct _ _ fs1, EStruct _ _ fs2) -> case op of 
--                                                        Eq  -> evalExpr' $ conj $ map (\(f1,f2) -> EBinOp nopos Eq f1 f2) $ zip fs1 fs2
--                                                        Neq -> evalExpr' $ disj $ map (\(f1,f2) -> EBinOp nopos Neq f1 f2) $ zip fs1 fs2
--                                                        _   -> error $ "Eval.evalExpr' " ++ show e
--             _                          -> EBinOp nopos op lhs' rhs'
-- evalExpr' (EUnOp _ op e)                = 
--     let e' = evalExpr' e
--     in case e' of
--            (EBool _ v) -> case op of
--                                Not -> EBool nopos (not v)
--            _           -> EUnOp nopos op e'
-- 
-- evalExpr' (ESlice _ e h l)              = case evalExpr' e of
--                                               EInt _ _ v -> EInt nopos (h-l+1) $ bitSlice v h l
--                                               e'         -> ESlice nopos e' h l
-- evalExpr' (ECond _ cs d)                = 
--     let cs1 = map (\(e1,e2) -> (evalExpr' e1, evalExpr' e2)) cs
--         cs2 = filter ((/= EBool nopos False) . fst) cs1
--         d'  = evalExpr' d
--     in case break ((== EBool nopos True) . fst) cs2 of 
--             ([],[])       -> d'
--             (cs3,[])      -> ECond nopos cs3 d'
--             ([],(_,e):_)  -> e
--             (cs3,(_,e):_) -> ECond nopos cs3 e
-- evalExpr' e                             = e
-- 
