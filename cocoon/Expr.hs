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

{-# LANGUAGE ImplicitParams, RecordWildCards, LambdaCase #-}

module Expr ( exprMapM
            , exprMap
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
            , exprSendsToPorts
            , exprSendsTo
            , exprUsesRels
            , isLExpr
            , isLVar
            , isLRel
            , exprSplitLHS
            , exprSplitVDecl
            , exprInline
            , expr2Statement
            , exprModifyResult
            , ctxExpectsStat
            , ctxMustReturn
            , exprIsStatement
            , exprVarSubst
            , exprVarRename
            , exprMutatorsNonRec
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
--import Debug.Trace

import Syntax
import NS
import Util
import Name
import {-# SOURCE #-} Type

-- depth-first fold of an expression
exprFoldCtxM :: (Monad m) => (ECtx -> ExprNode b -> m b) -> ECtx -> Expr -> m b
exprFoldCtxM f ctx (E n) = exprFoldCtxM' f ctx n

exprFoldCtxM' :: (Monad m) => (ECtx -> ExprNode b -> m b) -> ECtx -> ENode -> m b
exprFoldCtxM' f ctx   (EVar p v)          = f ctx $ EVar p v
exprFoldCtxM' f ctx   (EPacket p)         = f ctx $ EPacket p
exprFoldCtxM' f ctx e@(EBuiltin p fun as) = f ctx =<< (liftM $ EBuiltin p fun) (mapIdxM (\a i -> exprFoldCtxM f (CtxBuiltin e ctx i) a) as)
exprFoldCtxM' f ctx e@(EApply p fun as)   = f ctx =<< (liftM $ EApply p fun) (mapIdxM (\a i -> exprFoldCtxM f (CtxApply e ctx i) a) as)
exprFoldCtxM' f ctx e@(EField p s fl)     = do s' <- exprFoldCtxM f (CtxField e ctx) s
                                               f ctx $ EField p s' fl
exprFoldCtxM' f ctx e@(ELocation p r a d) = f ctx =<< (liftM $ \a' -> ELocation p r a' d) (exprFoldCtxM f (CtxLocation e ctx) a)
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
exprFoldCtxM' f ctx e@(EFor p v t c b)    = f ctx =<< (liftM2 $ EFor p v t) (exprFoldCtxM f (CtxForCond e ctx) c) 
                                                                            (exprFoldCtxM f (CtxForBody e ctx) b)
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
exprFoldCtxM' f ctx   (EAnon p)           = f ctx $ EAnon p
exprFoldCtxM' f ctx e@(ETyped p x t)      = do x' <- exprFoldCtxM f (CtxTyped e ctx) x
                                               f ctx $ ETyped p x' t
exprFoldCtxM' f ctx e@(ERelPred p rel as) = f ctx =<< (liftM $ ERelPred p rel) (mapIdxM (\a i -> exprFoldCtxM f (CtxRelPred e ctx i) a) as)
exprFoldCtxM' f ctx e@(EPut p rel v)      = f ctx =<< (liftM $ EPut p rel) (exprFoldCtxM f (CtxPut e ctx) v)
exprFoldCtxM' f ctx e@(EDelete p rel c)   = f ctx =<< (liftM $ EDelete p rel) (exprFoldCtxM f (CtxDelete e ctx) c)

exprMapM :: (Monad m) => (a -> m b) -> ExprNode a -> m (ExprNode b)
exprMapM g e = case e of
                   EVar p v           -> return $ EVar p v
                   EPacket p          -> return $ EPacket p
                   EBuiltin p f as    -> (liftM $ EBuiltin p f) $ mapM g as
                   EApply p f as      -> (liftM $ EApply p f) $ mapM g as
                   EField p s f       -> (liftM $ \s' -> EField p s' f) $ g s
                   ELocation p rl a d -> (liftM $ \a' -> ELocation p rl a' d) $ g a
                   EBool p b          -> return $ EBool p b
                   EInt p i           -> return $ EInt p i
                   EString p s        -> return $ EString p s
                   EBit p w v         -> return $ EBit p w v
                   EStruct p s fs     -> (liftM $ EStruct p s) $ mapM g fs
                   ETuple p fs        -> (liftM $ ETuple p) $ mapM g fs
                   ESlice p v h l     -> (liftM $ \v' -> ESlice p v' h l) $ g v
                   EMatch p m cs      -> (liftM2 $ EMatch p) (g m) $ mapM (\(e1, e2) -> liftM2 (,) (g e1) (g e2)) cs
                   EVarDecl p v       -> return $ EVarDecl p v
                   ESeq p l r         -> (liftM2 $ ESeq p) (g l) (g r)
                   EPar p l r         -> (liftM2 $ ESeq p) (g l) (g r)
                   EITE p i t me      -> (liftM3 $ EITE p) (g i) (g t) (maybe (return Nothing) (liftM Just . g) me)
                   EDrop p            -> return $ EDrop p
                   ESet p l r         -> (liftM2 $ ESet p) (g l) (g r)
                   ESend p d          -> (liftM $ ESend p) (g d)
                   EBinOp p op l r    -> (liftM2 $ EBinOp p op) (g l) (g r)
                   EUnOp p op v       -> (liftM $ EUnOp p op) (g v)
                   EFor p v t c b     -> (liftM2 $ EFor p v t) (g c) (g b)
                   EFork p v t c b    -> (liftM2 $ EFork p v t) (g c) (g b)
                   EWith p v t c b d  -> (liftM3 $ EWith p v t) (g c) (g b) (maybe (return Nothing) (liftM Just . g) d)
                   EAny p v t c b d   -> (liftM3 $ EAny p v t) (g c) (g b) (maybe (return Nothing) (liftM Just . g) d)
                   EPHolder p         -> return $ EPHolder p
                   EAnon p            -> return $ EAnon p
                   ETyped p v t       -> (liftM $ \v' -> ETyped p v' t) (g v)
                   ERelPred p rel as  -> (liftM $ ERelPred p rel) $ mapM g as
                   EPut p rel v       -> (liftM $ EPut p rel) $ g v
                   EDelete p rel c    -> (liftM $ EDelete p rel) $ g c


exprMap :: (a -> b) -> ExprNode a -> ExprNode b
exprMap f e = runIdentity $ exprMapM (\e' -> return $ f e') e

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
                                     EBuiltin _ _ as   -> foldl' op x' as
                                     EApply _ _ as     -> foldl' op x' as
                                     EField _ s _      -> x' `op` s
                                     ELocation _ _ a _ -> x' `op` a
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
                                     EFor _ _ _ c b    -> x' `op` c `op` b
                                     EFork _ _ _ c b   -> x' `op` c `op` b
                                     EWith _ _ _ c b d -> let x'' = x' `op` c `op` b in
                                                          maybe x'' (x'' `op`) d
                                     EAny _ _ _ c b d  -> let x'' = x' `op` c `op` b in
                                                          maybe x'' (x'' `op`) d
                                     EPHolder _        -> x'
                                     EAnon _           -> x'
                                     ETyped _ v _      -> x' `op` v
                                     ERelPred _ _ as   -> foldl' op x' as
                                     EPut _ _ v        -> x' `op` v
                                     EDelete _ _ c     -> x' `op` c


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
exprFuncs' acc e = nub $ exprCollect (\case
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
exprRefersToPkt' e = exprCollect (\case
                                   EPacket _    -> True
                                   _            -> False) (||) e

exprIsDeterministic :: Refine -> Expr -> Bool
exprIsDeterministic r e = exprIsDeterministic' e &&
                          (all (maybe True exprIsDeterministic' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsDeterministic' :: Expr -> Bool
exprIsDeterministic' e = exprCollect (\case
                                       EAny _ _ _ _ _ _ -> False
                                       _                -> True) (&&) e

exprIsMulticast :: Refine -> Expr -> Bool
exprIsMulticast r e = exprIsMulticast' e || 
                      (any (maybe False exprIsMulticast' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsMulticast' :: Expr -> Bool
exprIsMulticast' e = exprCollect (\case
                                   EPar _ _ _      -> True
                                   EFork _ _ _ _ _ -> True
                                   _               -> False) (||) e

exprSendsToPorts :: Refine -> Expr -> [DirPort]
exprSendsToPorts r e = nub $ exprSendsToPorts' e ++
                             (concatMap (maybe [] (exprSendsToPorts r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsToPorts' :: Expr -> [DirPort]
exprSendsToPorts' e = exprCollect (\case
                                    ELocation _ rl _ d -> [DirPort rl d]
                                    _                  -> []) 
                                  (++) e

exprSendsTo :: Refine -> Expr -> [Expr]
exprSendsTo r e = nub $ exprSendsTo' e ++
                        (concatMap (maybe [] (exprSendsTo r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsTo' :: Expr -> [Expr]
exprSendsTo' e = execState (exprTraverseM (\case
                                            ESend _ loc -> modify (loc:)
                                            _           -> return ()) e) []

exprUsesRels :: Refine -> Expr -> [String]
exprUsesRels r e = nub $ exprCollect (\case 
                                       EWith{..}    -> [exprTable]
                                       EAny{..}     -> [exprTable]
                                       EFor{..}     -> [exprTable]
                                       EFork{..}    -> [exprTable]
                                       EPut{..}     -> [exprTable]
                                       EDelete{..}  -> [exprTable]
                                       ERelPred{..} -> [exprRel]
                                       EApply{..}   -> maybe [] (exprUsesRels r) $ funcDef $ getFunc r exprFunc
                                       _            -> [])
                                     (++) e

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
isLExpr' _ _   (EAnon _)        = False
isLExpr' _ _   (ETyped _ e _)   = e
isLExpr' _ _   _                = False

isLVar :: Refine -> ECtx -> String -> Bool
isLVar r ctx v = isJust $ find ((==v) . name) $ fst $ ctxVars r ctx

isLRel :: Refine -> ECtx -> String -> Bool
isLRel r ctx rel = isJust $ find ((== rel) . name) $ fst $ ctxRels r ctx

-- Inline method bodies
exprInline :: Refine -> ECtx -> Expr -> Expr
exprInline r ctx e = exprFoldCtx (exprInline' r) ctx e'
    where e' = evalState (exprFoldM (exprPrecomputeArgs r) e) 0

-- compute arguments ahead of function invocations
exprPrecomputeArgs :: Refine -> ENode -> State Int Expr
exprPrecomputeArgs r (EApply _ f as) = do
    let Function{..} = getFunc r f
    let simple :: Expr -> Bool
        simple (E EVar{})         = True
        simple (E EBool{})        = True
        simple (E EBit{})         = True
        simple (E EInt{})         = True
        simple (E EString{})      = True
        simple (E (ETyped _ e _)) = simple e
        simple _                  = False
    (ps, as') <- liftM unzip
                 $ mapIdxM (\a i -> if simple a
                                       then return (Nothing, a)
                                       else do let t = typ $ funcArgs !! i
                                               arg <- allocArg
                                               let vdecl = eSet (eTyped (eVarDecl arg) t) a
                                               return (Just vdecl, eVar arg)) as
    return $ exprSequence $ (catMaybes ps) ++ [eApply f as']
exprPrecomputeArgs _ e = return $ E e

allocArg :: State Int String
allocArg = do modify (1+)
              liftM (("a#"++) . show) get

exprInline' :: Refine -> ECtx -> ENode -> Expr
exprInline' r ctx e@(EApply _ f as) | isJust funcDef = exprVarSubst subst vsubst body
                                    | otherwise      = E e
    where func@Function{..} = getFunc r f
          body = exprInline r (CtxFunc func ctx) $ fromJust funcDef
          -- rename local vars; substitute arguments
          subst v = case findIndex ((==v) . name) funcArgs of
                         Just i  -> as !! i
                         Nothing -> eVar $ f ++ ":" ++ v
          vsubst v = f ++ ":" ++ v
exprInline' _ _   e                                  = E e

-- every variable must be declared in a separate statement, e.g.,
-- (x, var y) = ...  ===> var y: Type; (x,y) = ...
--exprNormalizeVarDecls :: Refine -> ECtx -> Expr -> Expr
--exprNormalizeVarDecls = error "exprNormalizeVarDecls is undefined"


-- Convert expression to "statement" form, in which it can 
-- be easily translated into a statement-based language
expr2Statement :: Refine -> ECtx -> Expr -> State Int Expr
expr2Statement r ctx e = do 
    (_, e') <- exprFoldCtxM (expr2Statement_ r) ctx e
    return $ prefMerge e'

expr2Statement_ :: Refine -> ECtx -> ExprNode (Expr, ([Expr], Expr)) -> State Int (Expr, ([Expr], Expr))
expr2Statement_ r ctx e = do let orig = exprMap fst e
                             (p, e') <- expr2Statement' r ctx orig (exprMap snd e)
                             return (E orig, (p, e'))

expr2Statement' :: Refine -> ECtx -> ENode -> ExprNode ([Expr], Expr) -> State Int ([Expr], Expr)
expr2Statement' _ _   _ (EBuiltin _ f as)              = return (concatMap fst as, eBuiltin f $ map snd as)
expr2Statement' _ _   _ (EApply _ f as)                = return (concatMap fst as, eApply f $ map snd as)
expr2Statement' _ _   _ (EField _ (p,e) f)             = return (p, exprModifyResult (\e' -> eField e' f) e)
expr2Statement' _ _   _ (ELocation _ l (p,k) d)        = return (p, eLocation l k d)
expr2Statement' _ ctx e EStruct{} | ctxInMatchPat ctx  = return ([], E e)
expr2Statement' _ _   _ (EStruct _ c fs)               = return (concatMap fst fs, eStruct c $ map snd fs)
expr2Statement' _ _   _ (ETuple _ fs)                  = return (concatMap fst fs, eTuple $ map snd fs)
expr2Statement' _ _   _ (ESlice _ (p,e) h l)           = return (p, exprModifyResult (\e' -> eSlice e' h l) e)
expr2Statement' r ctx e (EMatch _ (p,m) cs)            = do (p', e'') <- exprPrecomputeVar ctx (extype r ctx $ E e) e'
                                                            return (p++p', e'')
    where e' = eMatch m $ map (\(c,v) -> (noprefMerge c, prefMerge v)) cs
expr2Statement' r ctx e (EITE _ (p,i) t me)            = do (p', e'') <- exprPrecomputeVar ctx (extype r ctx $ E e) e'
                                                            return (p++p', e'')
    where e' = eITE i (prefMerge t) (fmap prefMerge me)
expr2Statement' _ _   _ (ESet _ (pl,l) (pv,v))         = return (pl ++ pv, exprModifyResult (eSet l) v)
expr2Statement' _ _   _ (ESend _ (p,d))                = return (p, exprModifyResult eSend d)
expr2Statement' _ _   _ (EBinOp _ op (p1,e1) (p2,e2))  = return (p1 ++ p2, eBinOp op e1 e2)
expr2Statement' _ _   _ (EUnOp _ op (p,e))             = return (p, exprModifyResult (eUnOp op) e)
expr2Statement' _ _   _ (ETyped _ (p,e) t)             = return (p, exprModifyResult (\e' -> eTyped e' t) e)
expr2Statement' _ _   _ (EPut _ t (p,v))               = return (p, exprModifyResult (ePut t) v)
expr2Statement' _ _   _ (EDelete _ t c)                = return ([], eDelete t $ prefMerge c)
expr2Statement' r ctx e (EVarDecl _ vn) | operand ctx  = return ([eTyped (eVarDecl vn) $ extype r ctx $ E e], eVar vn)
                                        | otherwise    = return ([], eVarDecl vn)
expr2Statement' _ ctx _ (ESeq _ (p1,e1) (p2,e2)) | operand ctx = return (p1++[e1]++p2, e2)
                                                 | otherwise   = return ([], exprSequence $ p1 ++ [e1] ++ p2 ++ [e2])
expr2Statement' _ _   _ (EPar _ e1 e2)                 = return ([], ePar (prefMerge e1) (prefMerge e2))
expr2Statement' r ctx e (EWith _ v t c b md)           = exprPrecomputeVar ctx (extype r ctx $ E e) e'
    where e' = eWith v t (prefMerge c) (prefMerge b) (fmap prefMerge md)
expr2Statement' r ctx e (EAny _ v t c b md)            = exprPrecomputeVar ctx (exprType r ctx $ E e) e'
    where e' = eAny  v t (prefMerge c) (prefMerge b) (fmap prefMerge md)
expr2Statement' _ _   _ (EFor _ v t c b)               = return ([], eFor v t (prefMerge c) (prefMerge b))
expr2Statement' _ _   _ (EFork _ v t c b)              = return ([], eFork v t (prefMerge c) (prefMerge b))
expr2Statement' _ _   e EVar{}                         = return ([], E e)
expr2Statement' _ _   e EPacket{}                      = return ([], E e)
expr2Statement' _ _   e EBool{}                        = return ([], E e)
expr2Statement' _ _   e EBit{}                         = return ([], E e)
expr2Statement' _ _   e EInt{}                         = return ([], E e)
expr2Statement' _ _   e EString{}                      = return ([], E e)
expr2Statement' _ _   e EDrop{}                        = return ([], E e)
expr2Statement' _ _   e EPHolder{}                     = return ([], E e)
expr2Statement' _ _   e EAnon{}                        = return ([], E e)
expr2Statement' _ _   e ERelPred{}                     = error $ "Expr.expr2Statement " ++ show e

extype r ctx e = exprType r ctx e

prefMerge :: ([Expr], Expr) -> Expr
prefMerge (p,e) = exprSequence $ p++[e]

noprefMerge :: ([Expr], Expr) -> Expr
noprefMerge ([],e) = e
noprefMerge (p,e)  = error $ "Expr.expr2Statement: expect empty prefix" ++ show (p,e)

exprModifyResult :: (Expr -> Expr) -> Expr -> Expr
exprModifyResult f (E e) = exprModifyResult' f e

exprModifyResult' :: (Expr -> Expr) -> ENode -> Expr
exprModifyResult' f (EMatch _ m cs)      = eMatch m $ map (mapSnd $ exprModifyResult f) cs
exprModifyResult' f (ESet _ e1 e2)       = exprSequence [eSet e1 e2, f $ eTuple []]
exprModifyResult' f (ESeq _ e1 e2)       = eSeq e1 $ exprModifyResult f e2
exprModifyResult' f (EITE _ i t me)      = eITE i (exprModifyResult f t) (fmap (exprModifyResult f) me)
exprModifyResult' f (EWith _ v t c b md) = eWith v t c (exprModifyResult f b) (fmap (exprModifyResult f) md)
exprModifyResult' f (EAny _ v t c b md)  = eAny v t c (exprModifyResult f b) (fmap (exprModifyResult f) md)
exprModifyResult' f e                    = f $ E e

exprPrecomputeVar :: ECtx -> Type -> Expr -> State Int ([Expr], Expr)
exprPrecomputeVar ctx t e | operand ctx = do v <- allocVar
                                             let vdecl = eTyped (eVarDecl v) t
                                             return ([vdecl, exprModifyResult (eSet $ eVar v) e], eVar v)
                          | otherwise = return ([], e)

operand :: ECtx -> Bool
operand ctx = case ctx of
                   CtxApply{}     -> True
                   CtxBuiltin{}   -> True
                   CtxField{..}   -> operand ctxPar
                   CtxLocation{}  -> True
                   CtxStruct{}    -> True
                   CtxTuple{}     -> True
                   CtxSlice{..}   -> operand ctxPar
                   CtxMatchExpr{} -> True
                   CtxSeq2{..}    -> operand ctxPar
                   CtxITEIf{}     -> True
                   CtxSetL{}      -> True
                   CtxBinOpL{}    -> True
                   CtxBinOpR{}    -> True
                   CtxUnOp{..}    -> operand ctxPar
                   CtxTyped{..}   -> operand ctxPar
                   CtxPut{}       -> True
                   _              -> False

-- no structs or tuples in the LHS of an assignment, e.g.,
-- C{x,y} = f() ===> var z = f(); x = z.f1; y = z.f2
exprSplitLHS :: Refine -> ECtx -> Expr -> State Int Expr
exprSplitLHS r ctx e = exprFoldCtxM (exprSplitLHS' r) ctx e

exprSplitLHS' :: Refine -> ECtx -> ENode -> State Int Expr
exprSplitLHS' r ctx e@(ESet _ e'@(E (EStruct _ _ _)) rhs) = do 
    let t = exprType r (CtxSetR e ctx) rhs
    v <- allocVar
    let vdecl = eTyped (eVarDecl v) t
    let assigns = maybeToList $ setfield r (eVar v) (CtxSetL e ctx) e'
    return $ exprSequence $ vdecl : assigns
exprSplitLHS' _ _   e = return $ E e

setfield :: Refine -> Expr -> ECtx -> Expr -> Maybe Expr
setfield r (E e@(EStruct _ c fs)) ctx rhs  = 
    case catMaybes $ mapIdx (\(a, f) i -> setfield r f (CtxStruct e ctx i) (eField rhs $ name a)) $ zip as fs of
       [] -> Nothing
       es -> Just $ exprSequence es
    where Constructor _ _ as = getConstructor r c
setfield _ (E (EPHolder _)) _   _          = Nothing
setfield _ lhs              _   rhs        = Just $ eSet lhs rhs


allocVar :: State Int String
allocVar = do modify (1+)
              liftM (("v#"++) . show) get

-- no structs or tuples in the LHS of an assignment, e.g.,
-- C{x,y} = f() ===> var z = f(); x = z.f1; y = z.f2
exprSplitVDecl :: Refine -> ECtx -> Expr -> Expr
exprSplitVDecl r ctx e = exprFoldCtx (exprSplitVDecl' r) ctx e'
    where e' = exprFoldCtx (exprVDeclSetType r) ctx e
 
exprVDeclSetType :: Refine -> ECtx -> ENode -> Expr
exprVDeclSetType r ctx decl@(EVarDecl _ _) =
    case ctx of
        CtxTyped{} -> E decl
        _          -> eTyped (E decl) $ exprType r ctx $ E decl
exprVDeclSetType _ _   e = E e

exprSplitVDecl' :: Refine -> ECtx -> ENode -> Expr
exprSplitVDecl' _ _ (ESeq _ (E (ESet _ decl@(E (ETyped _ (E (EVarDecl _ v)) _)) rhs)) e2) = 
    eSeq decl (eSeq (eSet (eVar v) rhs) e2)
exprSplitVDecl' _ ctx eset@(ESet _ decl@(E (ETyped _ (E (EVarDecl _ v)) _)) rhs) = 
    case ctx of
        CtxSeq1 ESeq{} _ -> E eset
        _                -> eSeq decl (eSet (eVar v) rhs)
exprSplitVDecl' _ _   e = E e

ctxExpectsStat :: ECtx -> Bool
ctxExpectsStat CtxFunc{}     = True
ctxExpectsStat CtxMatchVal{} = True
ctxExpectsStat CtxSeq1{}     = True
ctxExpectsStat CtxSeq2{}     = True
ctxExpectsStat CtxPar1{}     = True
ctxExpectsStat CtxPar2{}     = True
ctxExpectsStat CtxITEThen{}  = True
ctxExpectsStat CtxITEElse{}  = True
ctxExpectsStat CtxForBody{}  = True
ctxExpectsStat CtxForkBody{} = True
ctxExpectsStat CtxWithBody{} = True
ctxExpectsStat CtxWithDef{}  = True
ctxExpectsStat CtxAnyBody{}  = True
ctxExpectsStat CtxAnyDef{}   = True
ctxExpectsStat _             = False

ctxMustReturn :: ECtx -> Bool
ctxMustReturn     CtxFunc{}       = True
ctxMustReturn     CtxSeq1{}       = False
ctxMustReturn     CtxPar1{}       = True
ctxMustReturn     CtxPar2{}       = True
ctxMustReturn     CtxForkBody{}   = True
ctxMustReturn ctx@CtxMatchVal{}   = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxSeq2{}       = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxITEThen{}    = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxITEElse{}    = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxWithBody{}   = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxWithDef{}    = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxAnyBody{}    = ctxMustReturn $ ctxParent ctx
ctxMustReturn ctx@CtxAnyDef{}     = ctxMustReturn $ ctxParent ctx
ctxMustReturn _                   = False

exprIsStatement :: ENode -> Bool
exprIsStatement (EMatch   {})                 = True
exprIsStatement (EVarDecl {})                 = True
exprIsStatement (ESeq     {})                 = True
exprIsStatement (EPar     {})                 = True
exprIsStatement (EITE     {})                 = True
exprIsStatement (EDrop    {})                 = True
exprIsStatement (ESet     {})                 = True
exprIsStatement (ESend    {})                 = True
exprIsStatement (EFor     {})                 = True
exprIsStatement (EFork    {})                 = True
exprIsStatement (EWith    {})                 = True
exprIsStatement (EAny     {})                 = True
exprIsStatement (ETyped _ (E (EVarDecl{})) _) = True
exprIsStatement (EPut _ _ _)                  = True
exprIsStatement (EDelete _ _ _)               = True
exprIsStatement _                             = False


exprVarSubst :: (String -> Expr) -> (String -> String) -> Expr -> Expr
exprVarSubst f h e = exprFold g e
    where g (EVar _ v)          = f v
          g (EVarDecl p v)      = E $ EVarDecl p $ h v
          g (EWith p v t c b d) = E $ EWith p (h v) t c b d
          g (EAny p v t c b d)  = E $ EAny p (h v) t c b d
          g (EFork p v t c b)   = E $ EFork p (h v) t c b
          g (EFor p v t c b)    = E $ EFor p (h v) t c b
          g e'                  = E e'

exprVarRename :: (String -> String) -> Expr -> Expr
exprVarRename f e = exprFold g e
    where g (EVar pos v) = E $ EVar pos $ f v
          g e'           = E e'

-- Returns subexpressions that mutate state, if any
exprMutatorsNonRec :: Expr -> [Expr]
exprMutatorsNonRec e = nub $ execState
    (exprFoldM (\e' -> do case e' of
                              EPut{}    -> modify (E e':)
                              EDelete{} -> modify (E e':)
                              _         -> return ()
                          return $ E e') e) 
    []
