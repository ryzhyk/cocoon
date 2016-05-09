{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Name where

class WithName a where
    name :: a -> String

instance WithName String where
    name = id
