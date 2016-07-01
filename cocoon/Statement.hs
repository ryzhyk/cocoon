{-
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
module Statement( statFold
                , statFuncsRec
                , statIsDeterministic
                , statIsMulticast
                , statSendsTo
                , statSendsToRoles) where

import Data.List

import Expr
import Syntax

statFold :: (a -> Statement -> a) -> a -> Statement -> a
statFold f acc s = 
   case s of 
        SSeq    _ l r   -> statFold f (statFold f acc' l) r
        SPar    _ l r   -> statFold f (statFold f acc' l) r
        SITE    _ _ t e -> maybe (statFold f acc' t) (statFold f (statFold f acc' t)) e
        STest   _ _     -> acc'
        SSet    _ _ _   -> acc'
        SSend   _ _     -> acc'
        SSendND _ _ _   -> acc'
        SHavoc  _ _     -> acc'
        SAssume _ _     -> acc'
        SLet    _ _ _ _ -> acc'
        SFork   _ _ _ b -> statFold f acc' b
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
          f fs (SLet _ _ _ v)  = fs ++ exprFuncsRec r v
          f fs (SFork _ _ c _) = fs ++ exprFuncsRec r c
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
statIsDeterministic (SLet    _ _ _ _) = True
statIsDeterministic (SFork   _ _ _ _) = True


statIsMulticast :: Statement -> Bool
statIsMulticast (SSeq    _ l r)   = statIsMulticast l || statIsMulticast r
statIsMulticast (SPar    _ _ _)   = True
statIsMulticast (SITE    _ _ t e) = statIsMulticast t || maybe False statIsMulticast e
statIsMulticast (STest   _ _ )    = False
statIsMulticast (SSet    _ _ _)   = False
statIsMulticast (SSend   _ _)     = False
statIsMulticast (SSendND _ _ _)   = False
statIsMulticast (SHavoc  _ _)     = False
statIsMulticast (SAssume _ _)     = False
statIsMulticast (SLet    _ _ _ _) = False
statIsMulticast (SFork   _ _ _ _) = True

statSendsToRoles :: Statement -> [String]
statSendsToRoles st = nub $ statSendsToRoles' st

statSendsToRoles' :: Statement -> [String]
statSendsToRoles' (SSeq  _ s1 s2)               = statSendsToRoles' s1 ++ statSendsToRoles' s2
statSendsToRoles' (SPar  _ s1 s2)               = statSendsToRoles' s1 ++ statSendsToRoles' s2
statSendsToRoles' (SITE  _ _ s1 s2)             = statSendsToRoles' s1 ++ (maybe [] statSendsToRoles' s2)
statSendsToRoles' (STest _ _)                   = []
statSendsToRoles' (SSet  _ _ _)                 = []
statSendsToRoles' (SSend _ (ELocation _ rl _))  = [rl]
statSendsToRoles' (SSend _ e)                   = error $ "statSendsToRoles' SSend " ++ show e
statSendsToRoles' (SHavoc _ _)                  = []
statSendsToRoles' (SAssume _ _)                 = []
statSendsToRoles' (SLet _ _ _ _)                = []
statSendsToRoles' (SSendND _ rl _)              = [rl]
statSendsToRoles' (SFork _ _ _ b)               = statSendsToRoles b


statSendsTo :: Statement -> [Expr]
statSendsTo st = nub $ statSendsTo' st

statSendsTo' :: Statement -> [Expr]
statSendsTo' (SSeq  _ s1 s2)   = statSendsTo' s1 ++ statSendsTo' s2
statSendsTo' (SPar  _ s1 s2)   = statSendsTo' s1 ++ statSendsTo' s2
statSendsTo' (SITE  _ _ s1 s2) = statSendsTo' s1 ++ (maybe [] statSendsTo' s2)
statSendsTo' (STest _ _)       = []
statSendsTo' (SSet  _ _ _)     = []
statSendsTo' (SSend _ loc)     = [loc]
statSendsTo' (SHavoc _ _)      = []
statSendsTo' (SAssume _ _)     = []
statSendsTo' (SLet _ _ _ _)    = []
statSendsTo' (SSendND _ _ _)   = error "statSendsTo' SSendND"
statSendsTo' (SFork _ _ _ _)   = error "statSendsTo' SFork"

