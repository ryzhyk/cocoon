module Statement( statFold
                , statFuncsRec
                , statIsDeterministic) where

import Data.List

import Expr
import Syntax

statFold :: (a -> Statement -> a) -> a -> Statement -> a
statFold f acc s = 
   case s of 
        SSeq    _ l r   -> f (f acc' l) r
        SPar    _ l r   -> f (f acc' l) r
        SITE    _ _ t e -> maybe (f acc' t) (f (f acc' t)) e
        STest   _ _     -> acc'
        SSet    _ _ _   -> acc'
        SSend   _ _     -> acc'
        SSendND _ _ _   -> acc'
        SHavoc  _ _     -> acc'
        SAssume _ _     -> acc'
   where acc' = f acc s

statFuncsRec :: Refine -> Statement -> [String]
statFuncsRec r s = nub $ statFold f [] s
    where f fs (SITE _ c _ _)  = fs ++ exprFuncsRec r c
          f fs (STest _ c)     = fs ++ exprFuncsRec r c
          f fs (SSet _ lv rv)  = fs ++ exprFuncsRec r lv ++ exprFuncsRec r rv
          f fs (SSend _ d)     = fs ++ exprFuncsRec r d
          f fs (SSendND _ _ c) = fs ++ exprFuncsRec r c
          f fs (SHavoc _ e)    = fs ++ exprFuncsRec r e
          f fs (SAssume _ c)   = fs ++ exprFuncsRec r c
          f fs _               = fs

statIsDeterministic :: Statement -> Bool
statIsDeterministic (SSeq    _ l r)   = statIsDeterministic l && statIsDeterministic r
statIsDeterministic (SPar    _ l r)   = statIsDeterministic l && statIsDeterministic r
statIsDeterministic (SITE    _ _ t e) = statIsDeterministic t && maybe True statIsDeterministic e
statIsDeterministic (STest   _ _ )    = True
statIsDeterministic (SSet    _ _ _)   = True
statIsDeterministic (SSend   _ _)     = True
statIsDeterministic (SSendND _ _ _)   = False
statIsDeterministic (SHavoc  _ _)     = False
statIsDeterministic (SAssume _ _)     = False
