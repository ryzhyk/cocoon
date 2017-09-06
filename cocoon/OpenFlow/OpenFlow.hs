{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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
{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards, OverloadedStrings #-}

-- Convert Cocoon spec to OpenFlow with Necera extensions

module OpenFlow.OpenFlow where

import Numeric
import Text.PrettyPrint

import Util
import Name
import PP

type Mask = Value

isFullMask :: Mask -> Bool
isFullMask (Value w v) = v == bitRange (w-1) 0

data Value = Value { valWidth :: Int
                   , valVal   :: Integer}
                   deriving (Eq)

instance Show Value where
    show (Value _ v) = showHex v ""

data Field = Field { fieldName  :: String
                   , fieldWidth :: Int}
                   deriving (Eq)

instance WithName Field where
    name = fieldName

instance PP Field where
    pp = pp . name

instance Show Field where
    show = render . pp

data Match = Match { matchField :: Field
                   , matchMask  :: Maybe Mask
                   , matchVal   :: Value
                   }

data Expr = EField Field (Maybe (Int, Int))
          | EVal   Value
            
instance PP Expr where
    pp (EField f Nothing)      = pp f <> "[]"
    pp (EField f (Just (h,l))) = pp f <> "[" <> pp l <> ".." <> pp h <> "]"
    pp (EVal v)                = pp $ valVal v
 

instance Show Expr where
    show = render . pp

exprIsConst :: Expr -> Bool
exprIsConst (EVal _) = True
exprIsConst _        = False

type HTable  = Int
type Prio    = Int
type GroupId = Int

data Action = ActionOutput {actPort :: Expr}
            | ActionGroup  {actGroup :: GroupId}
            | ActionDrop
            | ActionSet    {actLHS :: Expr, actRHS :: Expr}
            | ActionGoto   {actGotoTable :: HTable}

data Flow = Flow { flowPriority :: Prio
                 , flowMatch    :: [Match]
                 , flowActions  :: [Action]
                 }

data GroupType = GroupAll
               | GroupIndirect

instance PP GroupType where
    pp GroupAll      = "all"
    pp GroupIndirect = "indirect"

instance Show GroupType where
    show = render . pp

type BucketId = Int
data Bucket = Bucket (Maybe BucketId) [Action]

data Group = Group { groupId      :: GroupId 
                   , groupType    :: GroupType
                   , groupBuckets :: [Bucket]
                   }

data Command = AddFlow   HTable Flow
             | DelFlow   HTable Prio [Match]
             | AddGroup  Group
             | DelGroup  GroupId
             | AddBucket GroupId Bucket
             | DelBucket GroupId BucketId
