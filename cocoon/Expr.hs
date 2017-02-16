{-# LANGUAGE ImplicitParams #-}

module Expr ( exprFold
            , exprFoldM
            , exprTraverseM
            , exprFoldCtx
            , exprFoldCtxM
            , exprCollect
            , exprCollectM
            , exprFuncs
            , exprFuncsRec
            , exprRefersToPkt
            , exprIsMulticast
            , exprIsDeterministic
            , exprSendsToRoles
            , exprSendsTo
            --, exprScalars
            --, exprDeps
            --, exprSubst
            --, combineCascades
            ) where

import Data.List
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Syntax
import NS
import Util


-- depth-first fold of an expression
exprFoldCtxM :: (Monad m) => (ECtx -> ExprNode b -> m b) -> ECtx -> Expr -> m b
exprFoldCtxM f ctx (E n) = exprFoldCtxM' f ctx n

exprFoldCtxM' :: (Monad m) => (ECtx -> ExprNode b -> m b) -> ECtx -> ENode -> m b
exprFoldCtxM' f ctx   (EVar p v)          = f ctx $ EVar p v
exprFoldCtxM' f ctx   (EPacket p)         = f ctx $ EPacket p
exprFoldCtxM' f ctx e@(EApply p fun as)   = f ctx =<< (liftM $ EApply p fun) (mapIdxM (\a i -> exprFoldCtxM f (CtxApply e ctx i) a) as)
exprFoldCtxM' f ctx e@(EField p s fl)     = do s' <- exprFoldCtxM f (CtxField e ctx) s
                                               f ctx $ EField p s' fl
exprFoldCtxM' f ctx e@(ELocation p r a)   = f ctx =<< (liftM $ ELocation p r) (exprFoldCtxM f (CtxLocation e ctx) a)
exprFoldCtxM' f ctx   (EBool p b)         = f ctx $ EBool p b
exprFoldCtxM' f ctx   (EInt p i)          = f ctx $ EInt p i
exprFoldCtxM' f ctx   (EString p s)       = f ctx $ EString p s
exprFoldCtxM' f ctx   (EBit p w v)        = f ctx $ EBit p w v
exprFoldCtxM' f ctx e@(EStruct p c fs)    = f ctx =<< (liftM $ EStruct p c) (mapIdxM (\fl i -> exprFoldCtxM f (CtxStruct e ctx i) fl) fs)
exprFoldCtxM' f ctx e@(ETuple p fs)       = f ctx =<< (liftM $ ETuple p) (mapIdxM (\fl i -> exprFoldCtxM f (CtxTuple e ctx i) fl) fs)
exprFoldCtxM' f ctx e@(ESlice p v h l)    = do v' <- exprFoldCtxM f (CtxSlice e ctx) v
                                               f ctx $ ESlice p v' h l
exprFoldCtxM' f ctx e@(EMatch p m cs)     = do m' <- exprFoldCtxM f (CtxMatchExpr e ctx) m
                                               cs' <- mapIdxM (\(e1, e2) i -> liftM2 (,) (exprFoldCtxM f (CtxMatchPat e ctx i) e1) 
                                                                                         (exprFoldCtxM f (CtxMatchVal e ctx i) e2)) cs
                                               f ctx $ EMatch p m' cs'
exprFoldCtxM' f ctx   (EVarDecl p v)      = f ctx $ EVarDecl p v
exprFoldCtxM' f ctx e@(ESeq p l r)        = f ctx =<< (liftM2 $ ESeq p) (exprFoldCtxM f (CtxSeq1 e ctx) l) (exprFoldCtxM f (CtxSeq2 e ctx) r)
exprFoldCtxM' f ctx e@(EPar p l r)        = f ctx =<< (liftM2 $ EPar p) (exprFoldCtxM f (CtxPar1 e ctx) l) (exprFoldCtxM f (CtxPar2 e ctx) r)
exprFoldCtxM' f ctx e@(EITE p i t me)     = f ctx =<< (liftM3 $ EITE p) 
                                                      (exprFoldCtxM f (CtxITEIf e ctx) i) 
                                                      (exprFoldCtxM f (CtxITEThen e ctx) t) 
                                                      (maybe (return Nothing) ((liftM Just) . exprFoldCtxM f (CtxITEElse e ctx)) me)
exprFoldCtxM' f ctx   (EDrop p)           = f ctx $ EDrop p
exprFoldCtxM' f ctx e@(ESet p l r)        = f ctx =<< (liftM2 $ ESet p) (exprFoldCtxM f (CtxSetL e ctx) l) (exprFoldCtxM f (CtxSetR e ctx) r)
exprFoldCtxM' f ctx e@(ESend p d)         = f ctx =<< (liftM $ ESend p) (exprFoldCtxM f (CtxSend e ctx) d)
exprFoldCtxM' f ctx e@(EBinOp p op l r)   = f ctx =<< (liftM2 $ EBinOp p op) (exprFoldCtxM f (CtxBinOpL e ctx) l) 
                                                                             (exprFoldCtxM f (CtxBinOpR e ctx) r)
exprFoldCtxM' f ctx e@(EUnOp p op x)      = f ctx =<< (liftM $ EUnOp p op) (exprFoldCtxM f (CtxUnOp e ctx) x)
exprFoldCtxM' f ctx e@(EFork p v t c b)   = f ctx =<< (liftM2 $ EFork p v t) (exprFoldCtxM f (CtxForkCond e ctx) c) 
                                                                             (exprFoldCtxM f (CtxForkBody e ctx) b)
exprFoldCtxM' f ctx e@(EWith p v t c b d) = f ctx =<< (liftM3 $ EWith p v t) 
                                                      (exprFoldCtxM f (CtxWithCond e ctx) c) 
                                                      (exprFoldCtxM f (CtxWithBody e ctx) b)    
                                                      (maybe (return Nothing) ((liftM Just) . exprFoldCtxM f (CtxWithDef e ctx)) d)
exprFoldCtxM' f ctx e@(EAny p v t c b d)  = f ctx =<< (liftM3 $ EAny p v t) 
                                                      (exprFoldCtxM f (CtxAnyCond e ctx) c) 
                                                      (exprFoldCtxM f (CtxAnyBody e ctx) b)    
                                                      (maybe (return Nothing) ((liftM Just) . exprFoldCtxM f (CtxAnyDef e ctx)) d)
exprFoldCtxM' f ctx   (EPHolder p)        = f ctx $ EPHolder p
exprFoldCtxM' f ctx e@(ETyped p x t)      = do x' <- exprFoldCtxM f (CtxTyped e ctx) x
                                               f ctx $ ETyped p x' t


exprFoldCtx :: (ECtx -> ExprNode b -> b) -> ECtx -> Expr -> b
exprFoldCtx f ctx e = runIdentity $ exprFoldCtxM (\ctx' e' -> return $ f ctx' e') ctx e

exprFoldM :: (Monad m) => (ExprNode b -> m b) -> Expr -> m b
exprFoldM f e = exprFoldCtxM (\_ e' -> f e') undefined e

exprFold :: (ExprNode b -> b) -> Expr -> b
exprFold f e = runIdentity $ exprFoldM (return . f) e

exprTraverseM :: (Monad m) => (ENode -> m ()) -> Expr -> m ()
exprTraverseM f e = do {_ <- exprFoldM (\e' -> do {f e'; return $ E e'}) e; return ()}


exprCollectM :: (Monad m) => (ExprNode b -> m b) -> (b -> b -> b) -> Expr -> m b
exprCollectM f op e = exprFoldM g e
    where g x = do x' <- f x
                   return $ case x of
                                 EVar _ _          -> x'
                                 EPacket _         -> x'
                                 EApply _ _ as     -> foldl' op x' as
                                 EField _ s _      -> x' `op` s
                                 ELocation _ _ a   -> x' `op` a
                                 EBool _ _         -> x'
                                 EInt _ _          -> x'
                                 EString _ _       -> x'
                                 EBit _ _ _        -> x'
                                 EStruct _ _ fs    -> foldl' op x' fs
                                 ETuple _ fs       -> foldl' op x' fs
                                 ESlice _ v _ _    -> x' `op` v
                                 EMatch _ m cs     -> foldl' (\a (p,v) -> a `op` p `op` v) (x' `op` m) cs
                                 EVarDecl _ _      -> x'    
                                 ESeq _ l r        -> x' `op` l `op` r       
                                 EPar _ l r        -> x' `op` l `op` r       
                                 EITE _ i t me     -> let x'' = x' `op` i `op` t in 
                                                      maybe x'' (x'' `op`) me
                                 EDrop _           -> x'
                                 ESet _ l r        -> x' `op` l `op` r
                                 ESend _ d         -> x' `op` d        
                                 EBinOp _ _ l r    -> x' `op` l `op` r  
                                 EUnOp _ _ v       -> x' `op` v
                                 EFork _ _ _ c b   -> x' `op` c `op` b
                                 EWith _ _ _ c b d -> let x'' = x' `op` c `op` b in
                                                      maybe x'' (x'' `op`) d
                                 EAny _ _ _ c b d  -> let x'' = x' `op` c `op` b in
                                                      maybe x'' (x'' `op`) d
                                 EPHolder _        -> x'
                                 ETyped _ v _      -> x' `op` v


exprCollect :: (ExprNode b -> b) -> (b -> b -> b) -> Expr -> b
exprCollect f op e = runIdentity $ exprCollectM (return . f) op e

-- Non-recursively enumerate all functions invoked by the expression
exprFuncs :: Expr -> [String]
exprFuncs e = exprFuncs' [] e

exprFuncs' :: [String] -> Expr -> [String]
exprFuncs' acc e = nub $ exprCollect (\e' -> case e' of
                                                  EApply _ f _ -> if' (elem f acc) [] [f]
                                                  _            -> []) 
                                     (++) e

-- Recursively enumerate all functions invoked by the expression
exprFuncsRec :: Refine -> Expr -> [String]
exprFuncsRec r e = exprFuncsRec' r [] e

exprFuncsRec' :: Refine -> [String] -> Expr -> [String]
exprFuncsRec' r acc e = let new = exprFuncs' acc e in
                        new ++ foldl' (\acc' f -> maybe acc' ((acc'++) . exprFuncsRec' r (acc++new++acc')) $ funcDef $ getFunc r f) [] new

-- True if e does not refer to any packet fields 
-- (it may contain function calls and references to other variables)
exprRefersToPkt :: Refine -> Expr -> Bool
exprRefersToPkt r e = exprRefersToPkt' e || 
                      (any (maybe False exprRefersToPkt' . funcDef . getFunc r) $ exprFuncsRec r e)

exprRefersToPkt' :: Expr -> Bool
exprRefersToPkt' e = exprCollect (\e' -> case e' of
                                              EPacket _    -> True
                                              _            -> False) (||) e

exprIsDeterministic :: Refine -> Expr -> Bool
exprIsDeterministic r e = exprIsDeterministic' e &&
                          (all (maybe True exprIsDeterministic' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsDeterministic' :: Expr -> Bool
exprIsDeterministic' e = exprCollect (\e' -> case e' of
                                                  EAny _ _ _ _ _ _ -> False
                                                  _                -> True) (&&) e

exprIsMulticast :: Refine -> Expr -> Bool
exprIsMulticast r e = exprIsMulticast' e || 
                      (any (maybe False exprIsMulticast' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsMulticast' :: Expr -> Bool
exprIsMulticast' e = exprCollect (\e' -> case e' of
                                              EPar _ _ _      -> True
                                              EFork _ _ _ _ _ -> True
                                              _               -> False) (||) e

exprSendsToRoles :: Refine -> Expr -> [String]
exprSendsToRoles r e = nub $ exprSendsToRoles' e ++
                             (concatMap (maybe [] (exprSendsToRoles r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsToRoles' :: Expr -> [String]
exprSendsToRoles' e = exprCollect (\e' -> case e' of
                                               ELocation _ rl _ -> [rl]
                                               _                -> []) 
                                  (++) e

exprSendsTo :: Refine -> Expr -> [Expr]
exprSendsTo r e = nub $ exprSendsTo' e ++
                        (concatMap (maybe [] (exprSendsTo r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsTo' :: Expr -> [Expr]
exprSendsTo' e = execState (exprTraverseM (\e' -> case e' of
                                                       ESend _ loc -> modify (loc:)
                                                       _           -> return ()) e) []

{-
exprScalars :: Refine -> ECtx -> Expr -> [Expr]
exprScalars r c e = 
    case typ' r c e of
         TStruct _ fs -> concatMap (exprScalars r c . EField nopos e . name) fs
         _            -> [e]
-}

-- expression must be evaluated with evalExpr before calling this function
-- to eliminate subexpressions of the form structname{v1,v2}.f1
{-
exprDeps :: Expr -> [Expr]
exprDeps = nub . exprDeps' True

exprDeps' :: Bool -> Expr -> [Expr]
exprDeps' flag e@(EVar _ _)         = if' flag [e] []
exprDeps' flag e@(EDotVar _ _)      = if' flag [e] []
exprDeps' flag e@(EPacket _)        = if' flag [e] []
exprDeps' _      (EApply _ _ as)    = concatMap (exprDeps' True) as
exprDeps' _      (EBuiltin _ _ as)  = concatMap (exprDeps' True) as
exprDeps' flag e@(EField _ e' _)    = (if' (flag && isdep e) [e] []) ++ (exprDeps' False e')
    where isdep x = case x of
                         EVar _ _      -> True
                         EDotVar _ _   -> True
                         EPacket _     -> True
                         EField _ x' _ -> isdep x'
                         _             -> False
exprDeps' _      (ELocation _ _ _)  = error "Not implemented: exprDeps' ELocation"
exprDeps' _      (EBool _ _)        = []
exprDeps' _      (EInt _ _ _)       = []
exprDeps' _      (EStruct _ _ fs)   = concatMap (exprDeps' True) fs
exprDeps' _      (EBinOp _ _ e1 e2) = exprDeps' True e1 ++ exprDeps' True e2
exprDeps' _      (EUnOp _ _ e)      = exprDeps' True e
exprDeps' _      (ESlice _ e _ _)   = exprDeps' True e
exprDeps' _      (ECond _ cs d)     = (concatMap (\(c,v) -> exprDeps' True c ++ exprDeps' True v) cs) ++ exprDeps' True d

exprSubst :: Expr -> Expr -> Expr -> Expr
exprSubst arg val e               | e == arg = val
exprSubst _   _   e@(EVar _ _)               = e
exprSubst _   _   e@(EDotVar _ _)            = e
exprSubst _   _   e@(EPacket _)              = e
exprSubst arg val   (EApply _ f as)          = EApply nopos f $ map (exprSubst arg val) as
exprSubst arg val   (EBuiltin _ f as)        = EBuiltin nopos f $ map (exprSubst arg val) as
exprSubst arg val   (EField _ s f)           = EField nopos (exprSubst arg val s) f
exprSubst _   _     (ELocation _ _ _)        = error "Not implemented: exprSubst ELocation"
exprSubst _   _   e@(EBool _ _)              = e
exprSubst _   _   e@(EInt _ _ _)             = e
exprSubst arg val   (EStruct _ n fs)         = EStruct nopos n $ map (exprSubst arg val) fs
exprSubst arg val   (EBinOp _ op e1 e2)      = EBinOp nopos op (exprSubst arg val e1) (exprSubst arg val e2)
exprSubst arg val   (EUnOp _ op e)           = EUnOp nopos op $ exprSubst arg val e
exprSubst arg val   (ESlice _ e h l)         = ESlice nopos (exprSubst arg val e) h l
exprSubst arg val   (ECond _ cs d)           = ECond nopos (map (\(c,e) -> (exprSubst arg val c, exprSubst arg val e)) cs) $ exprSubst arg val d

combineCascades :: ([Expr] -> Expr) -> [Expr] -> Expr
combineCascades f es  = combineCascades' f es []

combineCascades' f ((ECond _ cs d):es) es' = ECond nopos (map (mapSnd (\v -> combineCascades' f (v:es) es')) cs) (combineCascades' f (d:es) es')
combineCascades' f (v:es) es'              = combineCascades' f es (es' ++ [v])
combineCascades' f [] es'                  = f es'
-}
