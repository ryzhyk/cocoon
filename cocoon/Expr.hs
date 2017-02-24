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

{-# LANGUAGE ImplicitParams #-}

module Expr ( exprMap
            , exprFold
            , exprFoldM
            , exprTraverseCtxWithM
            , exprTraverseCtxM
            , exprTraverseM
            , exprFoldCtx
            , exprFoldCtxM
            , exprCollectCtxM
            , exprCollectM
            , exprCollectCtx
            , exprCollect
            , exprVars
            , exprVarDecls
            , exprFuncs
            , exprFuncsRec
            , exprRefersToPkt
            , exprIsMulticast
            , exprIsDeterministic
            , exprSendsToRoles
            , exprSendsTo
            , isLExpr
            , isLVar
            , isLRel
            --, exprScalars
            --, exprDeps
            --, exprSubst
            --, combineCascades
            ) where

import Data.List
import Data.Maybe
import Control.Monad
import Control.Monad.Identity
import Control.Monad.State
import Debug.Trace

import Syntax
import NS
import Util
import Name

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
exprFoldCtxM' f ctx e@(ERelPred p rel as) = f ctx =<< (liftM $ ERelPred p rel) (mapIdxM (\a i -> exprFoldCtxM f (CtxRelPred e ctx i) a) as)

exprMap :: (Monad m) => (a -> m b) -> ExprNode a -> m (ExprNode b)
exprMap g e = case e of
                   EVar p v          -> return $ EVar p v
                   EPacket p         -> return $ EPacket p
                   EApply p f as     -> (liftM $ EApply p f) $ mapM g as
                   EField p s f      -> (liftM $ \s' -> EField p s' f) $ g s
                   ELocation p rl a  -> (liftM $ ELocation p rl) $ g a
                   EBool p b         -> return $ EBool p b
                   EInt p i          -> return $ EInt p i
                   EString p s       -> return $ EString p s
                   EBit p w v        -> return $ EBit p w v
                   EStruct p s fs    -> (liftM $ EStruct p s) $ mapM g fs
                   ETuple p fs       -> (liftM $ ETuple p) $ mapM g fs
                   ESlice p v h l    -> (liftM $ \v' -> ESlice p v' h l) $ g v
                   EMatch p m cs     -> (liftM2 $ EMatch p) (g m) $ mapM (\(e1, e2) -> liftM2 (,) (g e1) (g e2)) cs
                   EVarDecl p v      -> return $ EVarDecl p v
                   ESeq p l r        -> (liftM2 $ ESeq p) (g l) (g r)
                   EPar p l r        -> (liftM2 $ ESeq p) (g l) (g r)
                   EITE p i t me     -> (liftM3 $ EITE p) (g i) (g t) (maybe (return Nothing) (liftM Just . g) me)
                   EDrop p           -> return $ EDrop p
                   ESet p l r        -> (liftM2 $ ESet p) (g l) (g r)
                   ESend p d         -> (liftM $ ESend p) (g d)
                   EBinOp p op l r   -> (liftM2 $ EBinOp p op) (g l) (g r)
                   EUnOp p op v      -> (liftM $ EUnOp p op) (g v)
                   EFork p v t c b   -> (liftM2 $ EFork p v t) (g c) (g b)
                   EWith p v t c b d -> (liftM3 $ EWith p v t) (g c) (g b) (maybe (return Nothing) (liftM Just . g) d)
                   EAny p v t c b d  -> (liftM3 $ EAny p v t) (g c) (g b) (maybe (return Nothing) (liftM Just . g) d)
                   EPHolder p        -> return $ EPHolder p
                   ETyped p v t      -> (liftM $ \v' -> ETyped p v' t) (g v)
                   ERelPred p rel as -> (liftM $ ERelPred p rel) $ mapM g as

exprFoldCtx :: (ECtx -> ExprNode b -> b) -> ECtx -> Expr -> b
exprFoldCtx f ctx e = runIdentity $ exprFoldCtxM (\ctx' e' -> return $ f ctx' e') ctx e

exprFoldM :: (Monad m) => (ExprNode b -> m b) -> Expr -> m b
exprFoldM f e = exprFoldCtxM (\_ e' -> f e') undefined e

exprFold :: (ExprNode b -> b) -> Expr -> b
exprFold f e = runIdentity $ exprFoldM (return . f) e

exprTraverseCtxWithM :: (Monad m) => (ECtx -> ExprNode a -> m a) -> (ECtx -> ExprNode a -> m ()) -> ECtx -> Expr -> m ()
exprTraverseCtxWithM g f ctx e = do {_ <- exprFoldCtxM (\ctx' e' -> do {f ctx' e'; g ctx' e'}) ctx e; return ()}

exprTraverseCtxM :: (Monad m) => (ECtx -> ENode -> m ()) -> ECtx -> Expr -> m ()
exprTraverseCtxM = exprTraverseCtxWithM (\_ x -> return $ E x)

exprTraverseM :: (Monad m) => (ENode -> m ()) -> Expr -> m ()
exprTraverseM f = exprTraverseCtxM (\_ x -> f x) undefined


exprCollectCtxM :: (Monad m) => (ECtx -> ExprNode b -> m b) -> (b -> b -> b) -> ECtx -> Expr -> m b
exprCollectCtxM f op ctx e = exprFoldCtxM g ctx e
    where g ctx' x = do x' <- f ctx' x
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
                                     ERelPred _ _ as   -> foldl' op x' as


exprCollectM :: (Monad m) => (ExprNode b -> m b) -> (b -> b -> b) -> Expr -> m b
exprCollectM f op e = exprCollectCtxM (\_ e' -> f e') op undefined e

exprCollectCtx :: (ECtx -> ExprNode b -> b) -> (b -> b -> b) -> ECtx -> Expr -> b
exprCollectCtx f op ctx e = runIdentity $ exprCollectCtxM (\ctx' x -> return $ f ctx' x) op ctx e

exprCollect :: (ExprNode b -> b) -> (b -> b -> b) -> Expr -> b
exprCollect f op e = runIdentity $ exprCollectM (return . f) op e

-- enumerate all variables that occur in the expression
exprVars :: ECtx -> Expr -> [(String, ECtx)]
exprVars ctx e = exprCollectCtx (\ctx' e' -> case e' of
                                                  EVar _ v -> [(v, ctx')]
                                                  _        -> [])
                                (++) ctx e

-- Variables declared inside expression, visible in the code that follows the expression
exprVarDecls :: ECtx -> Expr -> [(String, ECtx)]
exprVarDecls ctx e = exprFoldCtx (\ctx' e' -> case e' of
                                                   EStruct _ _ fs -> concat fs
                                                   ETuple _ fs    -> concat fs
                                                   EVarDecl _ v   -> [(v, ctx')]
                                                   ESet _ l _     -> l
                                                   ETyped _ e'' _ -> e''
                                                   _              -> []) ctx e

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


isLExpr :: Refine -> ECtx -> Expr -> Bool
isLExpr r ctx e = exprFoldCtx (isLExpr' r) ctx e

isLExpr' :: Refine -> ECtx -> ExprNode Bool -> Bool
isLExpr' r ctx (EVar _ v)       = isLVar r ctx v
isLExpr' _ _   (EPacket _)      = True
isLExpr' _ _   (EField _ e _)   = e
isLExpr' _ _   (ETuple _ as)    = and as
isLExpr' _ _   (EStruct _ _ as) = and as
isLExpr' _ _   (EVarDecl _ _)   = True
isLExpr' _ _   (EPHolder _)     = True
isLExpr' _ _   (ETyped _ e _)   = e
isLExpr' _ _   _                = False

isLVar :: Refine -> ECtx -> String -> Bool
isLVar r ctx v = isJust $ lookup v $ fst $ ctxVars r ctx

isLRel :: Refine -> ECtx -> String -> Bool
isLRel r ctx rel = isJust $ find ((== rel) . name) $ fst $ ctxRels r ctx
