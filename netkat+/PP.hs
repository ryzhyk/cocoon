{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module PP(PP(..),
          nest',
          braces') where

import Text.PrettyPrint

ppshift = 4

-- pretty-printing class
class PP a where
    pp :: a -> Doc

instance PP String where
    pp s = text s

instance PP Int where
    pp = int

instance PP Bool where
    pp True  = text "true"
    pp False = text "false"

instance PP Integer where
    pp = integer

instance (PP a) => PP (Maybe a) where
    pp Nothing = empty
    pp (Just x) = pp x

nest' = nest ppshift
braces' x = lbrace $+$ nest' x $+$ rbrace

