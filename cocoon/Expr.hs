{-# LANGUAGE ImplicitParams #-}

module Expr ( exprFoldDF
            , exprFoldDFM
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

import Syntax
import NS
import Util

-- depth-first fold of an expression
exprFoldDF :: (a -> Expr -> a) -> a -> Expr -> a
exprFoldDF f x e@(EVar _ _)          = f x e
exprFoldDF f x e@(EPacket _)         = f x e
exprFoldDF f x e@(EApply _ _ as)     = f (foldl' f x as) e
exprFoldDF f x e@(EField _ s _)      = f (f x s) e
exprFoldDF f x e@(ELocation _ _ as)  = f (foldl' f x as) e
exprFoldDF f x e@(EBool _ _)         = f x e
exprFoldDF f x e@(EInt _ _)          = f x e
exprFoldDF f x e@(EString _ _)       = f x e
exprFoldDF f x e@(EBit _ _ _)        = f x e
exprFoldDF f x e@(EStruct _ _ fs)    = f (foldl' f x fs) e
exprFoldDF f x e@(ETuple _ fs)       = f (foldl' f x fs) e
exprFoldDF f x e@(ESlice _ op _ _)   = f (f x op) e
exprFoldDF f x e@(EMatch _ m cs)     = let x' = f x m in
                                       f (foldl' (\x'' (e1,e2) -> f (f x'' e1) e2) x' cs) e
exprFoldDF f x e@(EVarDecl _ _)      = f x e
exprFoldDF f x e@(ESeq _ l r)        = f (f (f x l) r) e
exprFoldDF f x e@(EPar _ l r)        = f (f (f x l) r) e
exprFoldDF f x e@(EITE _ i t me)     = let x' = f (f x i) t in
                                       f (maybe x' (f x') me) e
exprFoldDF f x e@(EDrop _)           = f x e
exprFoldDF f x e@(ESet _ l r)        = f (f (f x l) r) e
exprFoldDF f x e@(ESend _ d)         = f (f x d) e
exprFoldDF f x e@(EBinOp _ _ l r)    = f (f (f x l) r) e
exprFoldDF f x e@(EUnOp _ _ op)      = f (f x op) e
exprFoldDF f x e@(EFork _ _ _ c b)   = f (f (f x c) b) e
exprFoldDF f x e@(EWith _ _ _ c b d) = let x' = f (f x c) b in
                                       f (maybe x' (f x') d) e
exprFoldDF f x e@(EAny _ _ _ c b d)  = let x' = f (f x c) b in
                                       f (maybe x' (f x') d) e
exprFoldDF f x e@(EPHolder _)        = f x e
exprFoldDF f x e@(ETyped _ e' _)     = f (f x e') e


exprFoldDFM :: (Monad m) => (a -> Expr -> m a) -> a -> Expr -> m a
exprFoldDFM f x e@(EVar _ _)          = f x e
exprFoldDFM f x e@(EPacket _)         = f x e
exprFoldDFM f x e@(EApply _ _ as)     = do {x' <- foldM f x as; f x' e}
exprFoldDFM f x e@(EField _ s _)      = do {x' <- f x s; f x' e}
exprFoldDFM f x e@(ELocation _ _ as)  = do {x' <- foldM f x as; f x' e}
exprFoldDFM f x e@(EBool _ _)         = f x e
exprFoldDFM f x e@(EInt _ _)          = f x e
exprFoldDFM f x e@(EString _ _)       = f x e
exprFoldDFM f x e@(EBit _ _ _)        = f x e
exprFoldDFM f x e@(EStruct _ _ fs)    = do {x' <- foldM f x fs; f x' e}
exprFoldDFM f x e@(ETuple _ fs)       = do {x' <- foldM f x fs; f x' e}
exprFoldDFM f x e@(ESlice _ op _ _)   = do {x' <- f x op; f x' e}
exprFoldDFM f x e@(EMatch _ m cs)     = do x'  <- f x m
                                           x'' <- foldM (\x'' (e1,e2) -> do {y <- (f x'' e1); f y e2}) x' cs
                                           f x'' e
exprFoldDFM f x e@(EVarDecl _ _)      = f x e
exprFoldDFM f x e@(ESeq _ l r)        = do {x' <- f x l; x'' <- f x' r; f x'' e}
exprFoldDFM f x e@(EPar _ l r)        = do {x' <- f x l; x'' <- f x' r; f x'' e}
exprFoldDFM f x e@(EITE _ i t me)     = do x'  <- f x i
                                           x'' <- f x' t
                                           x''' <- maybe (return x'') (f x'') me
                                           f x''' e
exprFoldDFM f x e@(EDrop _)           = f x e
exprFoldDFM f x e@(ESet _ l r)        = do {x' <- f x l; x'' <- f x' r; f x'' e}
exprFoldDFM f x e@(ESend _ d)         = do {x' <- f x d; f x' e}
exprFoldDFM f x e@(EBinOp _ _ l r)    = do {x' <- f x l; x'' <- f x' r; f x'' e}
exprFoldDFM f x e@(EUnOp _ _ op)      = do {x' <- f x op; f x' e}
exprFoldDFM f x e@(EFork _ _ _ c b)   = do {x' <- f x c; x'' <- f x' b; f x'' e}
exprFoldDFM f x e@(EWith _ _ _ c b d) = do x' <- f x c
                                           x'' <- f x' b
                                           x''' <- maybe (return x'') (f x'') d
                                           f x''' e
exprFoldDFM f x e@(EAny _ _ _ c b d)  = do x' <- f x c
                                           x'' <- f x' b
                                           x''' <- maybe (return x'') (f x'') d
                                           f x''' e
exprFoldDFM f x e@(EPHolder _)        = f x e
exprFoldDFM f x e@(ETyped _ e' _)     = do {x' <- f x e'; f x' e}


-- Non-recursively enumerate all functions invoked by the expression
exprFuncs :: Expr -> [String]
exprFuncs e = exprFoldDF (\fs e' -> case e' of
                                         EApply _ f _ -> if' (elem f fs) fs (f:fs)
                                         _            -> fs) [] e

-- Recursively enumerate all functions invoked by the expression
exprFuncsRec :: Refine -> Expr -> [String]
exprFuncsRec r e = exprFuncsRec' r [] e

exprFuncsRec' :: Refine -> [String] -> Expr -> [String]
exprFuncsRec' r acc e = exprFoldDF (\fs e' -> case e' of
                                                   EApply _ f _ -> let mdef = funcDef $ getFunc r f in
                                                                   if' (elem f fs) fs
                                                                       (maybe (f:fs) (exprFuncsRec' r (f:fs)) mdef)
                                                   _            -> fs) acc e

-- True if e does not refer to any packet fields 
-- (it may contain function calls and references to other variables)
exprRefersToPkt :: Refine -> Expr -> Bool
exprRefersToPkt r e = exprRefersToPkt' e || 
                      (any (maybe False exprRefersToPkt' . funcDef . getFunc r) $ exprFuncsRec r e)

exprRefersToPkt' :: Expr -> Bool
exprRefersToPkt' e = exprFoldDF (\a e' -> case e' of
                                              EPacket _    -> True
                                              _            -> a) False e

exprIsDeterministic :: Refine -> Expr -> Bool
exprIsDeterministic r e = exprIsDeterministic' e &&
                          (all (maybe True exprIsDeterministic' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsDeterministic' :: Expr -> Bool
exprIsDeterministic' e = exprFoldDF (\a e' -> case e' of
                                                   EAny _ _ _ _ _ _ -> False
                                                   _                -> a) True e

exprIsMulticast :: Refine -> Expr -> Bool
exprIsMulticast r e = exprIsMulticast' e || 
                      (any (maybe False exprIsMulticast' . funcDef . getFunc r) $ exprFuncsRec r e)

exprIsMulticast' :: Expr -> Bool
exprIsMulticast' e = exprFoldDF (\a e' -> case e' of
                                               EPar _ _ _      -> True
                                               EFork _ _ _ _ _ -> True
                                               _               -> a) False e


exprSendsToRoles :: Refine -> Expr -> [String]
exprSendsToRoles r e = nub $ exprSendsToRoles' e ++
                             (concatMap (maybe [] (exprSendsToRoles r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsToRoles' :: Expr -> [String]
exprSendsToRoles' e = exprFoldDF (\a e' -> case e' of
                                                ESend _ (ELocation _ rl _) -> if' (elem rl a) a (rl:a)
                                                _                          -> a) [] e

exprSendsTo :: Refine -> Expr -> [Expr]
exprSendsTo r e = {-nub $-} exprSendsTo' e ++
                            (concatMap (maybe [] (exprSendsTo r) . funcDef . getFunc r) $ exprFuncsRec r e)

exprSendsTo' :: Expr -> [Expr]
exprSendsTo' e = exprFoldDF (\a e' -> case e' of
                                           ESend _ loc -> loc:a
                                           _           -> a) [] e

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
