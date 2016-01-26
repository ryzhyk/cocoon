{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Name where

class WithName a where
    name :: a -> String

sname :: (WithName a) => a -> String
sname x = show $ name x

instance WithName String where
    name = id
