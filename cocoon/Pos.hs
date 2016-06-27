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

module Pos(Pos, 
           WithPos(..),
           spos,
           nopos,
           posInside) where

import Text.Parsec.Pos

type Pos = (SourcePos,SourcePos)

class WithPos a where
    pos   :: a -> Pos
    atPos :: a -> Pos -> a

instance WithPos Pos where
    pos       = id
    atPos _ p = p

spos :: (WithPos a) => a -> String
spos x = let p = fst $ pos x
         in sourceName p ++ ":" ++ (show $ sourceLine p) ++ ":" ++ (show $ sourceColumn p)

nopos::Pos 
nopos = (initialPos "",initialPos "")

posInside :: SourcePos -> Pos -> Bool
posInside p (p1, p2) = sourceLine p >= sourceLine p1 && sourceLine p <= sourceLine p2 &&
                       (if sourceLine p == sourceLine p1
                           then sourceColumn p >= sourceColumn p1
                           else True) &&
                       (if sourceLine p == sourceLine p2
                           then sourceColumn p <= sourceColumn p2
                           else True)

