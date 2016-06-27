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
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module PP(PP(..),
          nest',
          braces') where

import Text.PrettyPrint

ppshift :: Int
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

nest' :: Doc -> Doc
nest' = nest ppshift

braces' :: Doc -> Doc
braces' x = lbrace $+$ nest' x $+$ rbrace

