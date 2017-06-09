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
            , MENode
            , MExpr(..)
            , EvalState
            , eget
            , eput
            , emodify
            , eyield
            , evalExpr) where

import qualified Data.Map as M
import Data.Maybe
import Data.Bits 
import Data.List
import Control.Monad.State.Strict
import Text.PrettyPrint

import Expr
import qualified SMT           as SMT
import qualified SMT.SMTSolver as SMT
import qualified SMT.Datalog   as DL
import Syntax
import Type
import Name
import NS
import Util
import Pos
import PP
import {-# SOURCE #-} Builtins

type MENode = Maybe (ExprNode MExpr)

newtype MExpr = ME MENode

instance PP MExpr where
    pp (ME n) = pp n

instance Show MExpr where
    show = render . pp

meField  s f   = ME $ Just $ EField  nopos s f
meBit    w v   = ME $ Just $ EBit    nopos w v
meBool   b     = ME $ Just $ EBool   nopos b
meSlice  e h l = ME $ Just $ ESlice  nopos e h l
meTuple  vs    = ME $ Just $ ETuple  nopos vs
meStruct c fs  = ME $ Just $ EStruct nopos c fs
meUnOp   op e  = ME $ Just $ EUnOp   nopos op e
meNot          = meUnOp Not

-- Key map: maps keys into their values
type KMap = M.Map String MExpr

type EvalState a = StateT (KMap, [Expr]) IO a

eget :: EvalState KMap
eget = gets fst

eput :: KMap -> EvalState ()
eput kmap = modify $ \(_,y) -> (kmap, y)

emodify :: (KMap -> KMap) -> EvalState ()
emodify f = modify $ \(m, y) -> (f m, y)

eyield :: Expr -> EvalState ()
eyield e = modify $ \(m,y) -> (m, y ++ [e])

evalExpr :: Refine -> ECtx -> KMap -> DL.Session -> Expr -> IO ([Expr], KMap)
evalExpr r ctx kmap dl e = do let ?dl = dl      
                                  ?r = r 
                              (res, (kmap', ys)) <- runStateT (evalExpr' ctx e) (kmap, [])
                              res' <- mexpr2Expr res
                              return (ys ++ [res'], kmap')

evalExpr' :: (?r::Refine, ?dl::DL.Session) => ECtx -> Expr -> EvalState MExpr
evalExpr' ctx (E e) = evalExpr'' ctx e

-- "strict" version -- requires expession to be fully assigned
evalExprS :: (?r::Refine, ?dl::DL.Session) => ECtx -> Expr -> EvalState Expr
evalExprS ctx e = evalExpr' ctx e >>= (lift . mexpr2Expr)

evalExpr'' :: (?r::Refine, ?dl::DL.Session) => ECtx -> ENode -> EvalState MExpr
evalExpr'' ctx e = do
    case e of
        EVar _ v        -> (liftM (M.! v)) eget
        EApply _ f as   -> do let fun = getFunc ?r f
                              kmap' <- liftM M.fromList 
                                       $ liftM (zip (map name $ funcArgs fun)) 
                                       $ mapIdxM (\a i -> evalExpr' (CtxApply e ctx i) a) as
                              kmap <- eget
                              eput kmap'
                              v <- evalExpr' (CtxFunc fun ctx) (fromJust $ funcDef fun)
                              eput kmap
                              return v
        EBuiltin _ f as -> do let bin = getBuiltin f
                              as' <- mapIdxM (\a i -> evalExprS (CtxBuiltin e ctx i) a) as
                              (liftM expr2MExpr) $ (bfuncEval bin) $ eBuiltin f as'
        EField _ s f    -> do ME s' <- evalExpr' (CtxField e ctx) s
                              when (isNothing s') $ error $ show s ++ " has not been assigned at " ++ show (pos e)
                              case fromJust s' of
                                   EStruct _ c fs -> do let cons = getConstructor ?r c
                                                        fidx <- maybe (error $ "field " ++ f ++ " does not exist in expression " ++ show e ++ " at " ++ show (pos e)) return
                                                                         $ findIndex ((==f) . name) $ consArgs cons
                                                        return $ fs !! fidx
                                   _              -> return $ meField (ME s') f
        EBool{}         -> return $ expr2MExpr $ E e
        EInt{}          -> return $ case exprType ?r ctx (E e) of
                                         TInt _   -> expr2MExpr $ E e
                                         TBit _ w -> meBit w (exprIVal e)
                                         _        -> error $ "EVal.evalExpr EInt " ++ show e
        EString{}       -> return $ expr2MExpr $ E e
        EBit{}          -> return $ expr2MExpr $ E e
        EStruct _ c fs  -> liftM (meStruct c) $ mapIdxM (\f i -> evalExpr' (CtxStruct e ctx i) f) fs
        ETuple _ fs     -> liftM meTuple $ mapIdxM (\f i -> evalExpr' (CtxTuple e ctx i) f) fs
        ESlice _ op h l -> do op' <- evalExprS (CtxSlice e ctx) op
                              return $ case enode op' of
                                            EBit _ w v -> meBit w $ bitSlice v h l
                                            _          -> meSlice (expr2MExpr op') h l
        EMatch _ m cs   -> do m' <- evalExprS (CtxMatchExpr e ctx) m
                              case findIndex (match m' . fst) cs of
                                   Just i      -> do let (c, v) = cs !! i
                                                     kmap <- eget
                                                     assignTemplate (CtxMatchPat e ctx i) c $ expr2MExpr m'
                                                     v' <- evalExpr' (CtxMatchVal e ctx i) v
                                                     eput kmap
                                                     return v'
                                   Nothing     -> error $ "No match found in\n" ++ show e ++ 
                                                          "\nwhere match expression evaluates to " ++ show m'
        EVarDecl _ v    -> do let v' = emptyVal $ exprType ?r ctx $ E e
                              emodify $ M.insert v v'
                              return v'
        ESeq _ e1 e2    -> do _ <- evalExpr' (CtxSeq1 e ctx) e1
                              evalExpr' (CtxSeq2 e ctx) e2
        EITE _ c t el   -> do E c' <- evalExprS (CtxITEIf e ctx) c
                              case c' of
                                   EBool _ True  -> evalExpr' (CtxITEThen e ctx) t
                                   EBool _ False -> maybe (return $ meTuple [])
                                                          (evalExpr' (CtxITEElse e ctx))
                                                          el
                                   _             -> error $ "Condition does not evaluate to a constant in\n" ++ show e
        ESet _ l r      -> do r' <- evalExpr' (CtxSetR e ctx) r
                              assignTemplate (CtxSetL e ctx) l r'
                              return $ meTuple []
        EBinOp _ op l r -> do l' <- evalExprS (CtxBinOpL e ctx) l
                              r' <- evalExprS (CtxBinOpR e ctx) r
                              return $ expr2MExpr $ evalBinOp $ eBinOp op l' r'
        EUnOp  _ Not a -> do E a' <- evalExprS (CtxUnOp e ctx) a
                             return $ case a' of
                                           EBool _ v -> meBool $ not v
                                           _         -> meNot $ expr2MExpr $ E a'
        EFor _ v t c b -> do let rel = getRelation ?r t
                             rows <- lift $ (liftM $ map (assignment2Row rel)) $ DL.enumRelation ?dl t
                             mapM_ (\row -> do kmap <- eget
                                               emodify $ M.insert v $ expr2MExpr row
                                               lift $ putStrLn $ "row: " ++ show row
                                               E c' <- evalExprS (CtxForCond e ctx) c
                                               lift $ putStrLn $ "c': " ++ show c'
                                               case c' of
                                                    EBool{} -> return ()
                                                    _       -> error $ "Query condition does not evaluate to a constant in\n" ++ show e ++ "\nrow: " ++ show row ++ " c': " ++ show c' 
                                               when (exprBVal c') $ do _ <- evalExpr' (CtxForBody e ctx) b
                                                                       return ()
                                               eput kmap)
                                   rows
                             return $ meTuple []
        EWith _ v t c b d -> do let rel = getRelation ?r t
                                rows <- lift $ (liftM $ map (assignment2Row rel)) $ DL.enumRelation ?dl t
                                rows' <- filterM (\row -> do kmap <- eget
                                                             emodify $ M.insert v $ expr2MExpr row
                                                             E c' <- evalExprS (CtxWithCond e ctx) c
                                                             case c' of
                                                                  EBool{} -> return ()
                                                                  _       -> error $ "Query condition does not evaluate to a constant in\n" ++ show e
                                                             eput kmap
                                                             return $ exprBVal c') 
                                                 rows
                                case rows' of
                                     [row] -> do kmap <- eget
                                                 emodify $ M.insert v $ expr2MExpr row
                                                 res <- evalExpr' (CtxWithBody e ctx) b
                                                 eput kmap
                                                 return res
                                     []    -> maybe (error $ "query returned no rows in\n" ++ show e)
                                                    (\d' -> evalExpr' (CtxWithDef e ctx) d')
                                                    d
                                     _     -> error $ "query returned multiple rows in\n" ++ show e ++ ":\n" ++
                                                      (intercalate "\n" $ map show rows') 
        ETyped _ v _        -> evalExpr' (CtxTyped e ctx) v
        _                   -> error $ "Eval.evalExpr " ++ show e

emptyVal :: (?r::Refine) => Type -> MExpr
emptyVal t = emptyVal' $ typ' ?r t

emptyVal' :: Type -> MExpr
emptyVal' (TStruct _ [c]) = meStruct (name c) $ map (\_ -> ME Nothing) $ consArgs c
emptyVal' (TTuple _ as)   = meTuple $ map (\_ -> ME Nothing) as
emptyVal' _               = ME Nothing

mexpr2Expr :: MExpr -> IO Expr
mexpr2Expr (ME Nothing)  = error "not assigned"
mexpr2Expr (ME (Just e)) = liftM E $ exprMapM mexpr2Expr e

expr2MExpr :: Expr -> MExpr
expr2MExpr = exprFold (\e -> ME $ Just e)

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
 

assignTemplate :: (?r::Refine, ?dl::DL.Session) => ECtx -> Expr -> MExpr -> EvalState ()
assignTemplate ctx (E l) r@(ME mr) = 
    case (l, mr) of
         (EVar _ v,        _)                -> emodify $ M.insert v r
         (EField _ e f,    _)                -> do ME me <- evalExpr' (CtxField l ctx) e
                                                   when (isNothing me) $ error $ show e ++ " has not been assigned at " ++ show (pos e)
                                                   let Just (EStruct _ c fs) = me
                                                   let cons = getConstructor ?r c
                                                   case findIndex ((== f) . name) $ consArgs cons of 
                                                        Nothing -> error $ "field " ++ f ++ " does not exist in " ++ show e ++ " at " ++ show (pos e)
                                                        Just i  -> let e' = meStruct c $ (take i fs) ++ (r : (drop (i+1) fs)) in
                                                                   assignTemplate (CtxField l ctx) e e'
         (ETuple _ _,     Nothing)           -> error $ "right-hand side expression has not been assigned at " ++ show (pos l)
         (ETuple _ ls,    Just (ETuple _ rs))-> mapIdxM_ (\(l', r') i -> assignTemplate (CtxTuple l ctx i) l' r') 
                                                         $ zip ls rs 
         (EStruct _ _ _,   Nothing)          -> error $ "right-hand side expression has not been assigned at " ++ show (pos l)
         (EStruct _ lc ls, Just (EStruct _ rc rs)) | lc == rc  -> mapIdxM_ (\(l',r') i -> assignTemplate (CtxStruct l ctx i) l' r') 
                                                                           $ zip ls rs
                                                   | otherwise -> error $ "constructor mismatch at " ++ show (pos l) ++ 
                                                                          ": assigning " ++ rc ++ " to " ++ lc
         (EVarDecl _ v,    _)                -> emodify $ M.insert v r
         (EPHolder _,      _)                -> return ()
         (ETyped _ e _,    _)                -> assignTemplate (CtxTyped l ctx) e r
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
         (EBit _ w v1, EInt _ v2)     -> case op of
                                            Eq     -> eBool (v1 == v2)
                                            Neq    -> eBool (v1 /= v2)
                                            Lt     -> eBool (v1 < v2)
                                            Gt     -> eBool (v1 > v2)
                                            Lte    -> eBool (v1 <= v2)
                                            Gte    -> eBool (v1 >= v2)
                                            Plus   -> eBit  w ((v1 + v2) `mod` (1 `shiftL` w))
                                            Minus  -> eBit  w ((v1 - v2) `mod` (1 `shiftL` w))
                                            ShiftR -> eBit  w (v1 `shiftR` fromInteger(v2))
                                            ShiftL -> eBit  w ((v1 `shiftL` fromInteger(v2)) `mod` (1 `shiftL` w))
                                            Mod    -> eBit  w (v1 `mod` v2)
                                            _      -> error $ "Eval.evalBinOp " ++ show e
         (EInt _ v1, EBit _ w v2)     -> case op of
                                            Eq     -> eBool (v1 == v2)
                                            Neq    -> eBool (v1 /= v2)
                                            Lt     -> eBool (v1 < v2)
                                            Gt     -> eBool (v1 > v2)
                                            Lte    -> eBool (v1 <= v2)
                                            Gte    -> eBool (v1 >= v2)
                                            Plus   -> eBit  w ((v1 + v2) `mod` (1 `shiftL` w))
                                            Minus  -> eBit  w ((v1 - v2) `mod` (1 `shiftL` w))
                                            ShiftR -> eInt  (v1 `shiftR` fromInteger(v2))
                                            ShiftL -> eInt  (v1 `shiftL` fromInteger(v2))
                                            Mod    -> eInt (v1 `mod` v2)
                                            _      -> error $ "Eval.evalBinOp " ++ show e
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
