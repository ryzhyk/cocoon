{-# LANGUAGE FlexibleContexts #-}

module Util where

import Data.Graph.Inductive
import Control.Monad.Except
import Data.List
import Data.Maybe

import Pos
import Name 


err :: (MonadError String me) => Pos -> String -> me a
err p e = throwError $ spos p ++ ": " ++ e

assert :: (MonadError String me) => Bool -> Pos -> String -> me ()
assert b p m = 
    if b 
       then return ()
       else err p m

-- Check for duplicate declarations
uniq :: (MonadError String me, WithPos a, Ord b) => (a -> b) -> (a -> String) -> [a] -> me ()
uniq ford msgfunc xs = do
    case filter ((>1) . length) $ groupBy (\x1 x2 -> compare (ford x1) (ford x2) == EQ)  
                                $ sortBy (\x1 x2 -> compare (ford x1) (ford x2)) xs of
         []        -> return ()
         g@(x:_):_ -> err (pos x) $ msgfunc x ++ " at the following locations:\n  " ++ (intercalate "\n  " $ map spos g)

uniqNames :: (MonadError String me, WithPos a, WithName a) => (String -> String) -> [a] -> me ()
uniqNames msgfunc = uniq name (\x -> msgfunc (name x))

-- Find a cycle in a graph
grCycle :: Graph gr => gr a b -> Maybe [LNode a]
grCycle g = case mapMaybe nodeCycle (nodes g) of
                 []  -> Nothing
                 c:_ -> Just c
  where
    nodeCycle n = listToMaybe $ map (\s -> map (\id -> (id, fromJust $ lab g id)) (n:(esp s n g))) $ 
                                filter (\s -> elem n (reachable s g)) $ suc g n

--Logarithm to base 2. Equivalent to floor(log2(x))
log2 :: Integer -> Int
log2 0 = 0
log2 1 = 0
log2 n 
    | n>1 = 1 + log2 (n `div` 2)
    | otherwise = error "log2: negative argument"

-- The number of bits required to encode range [0..i]
bitWidth :: (Integral a) => a -> Int
bitWidth i = 1 + log2 (fromIntegral i)
