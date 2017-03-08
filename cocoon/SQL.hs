{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 

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

{-# LANGUAGE RecordWildCards #-}

-- Cocoon's SQL backend

module SQL (mkSchema) where

import Data.List.Utils
import Data.Bits
import Text.PrettyPrint

import Name
import PP
import Util
import Syntax
import Type
import NS

-- Special tables
-- * Connection tracker
-- (* ACL )
-- primary key in a view
    -- has primary key - OK
    -- otherwise, pick a unique key that's always present
    -- otherwise, use a combination of all fields

-- Where are relations stored

-- TODO: for purely local state (only read and written by a single switch),
-- store the table on switche's local controller
mkSchema :: Refine -> Doc
mkSchema r@Refine{..} = vcat rels
    where rels = map (mkRel r) refineRels
          -- funs = map (mkFun r) $ -- functions used in constraints

mkRel :: Refine -> Relation -> Doc
mkRel r rel@Relation{..} = pp "create table" <+> pp relName <+> pp "("
                           $$
                           (nest' $ vcat $ punctuate comma $ cols ++ cons)
                           $$
                           pp ");"
    where
    -- Primary table
    cols = map (mkColumn r rel) relArgs
    cons = map (mkConstraint r rel) relConstraints
    -- View query
    -- Delta table
    -- rel' = 
    -- Primary-delta synchronization triggers

mkColumn :: Refine -> Relation -> Field -> Doc
mkColumn r rel f = mkColumn' r rel $ eVar $ name f

mkColumn' :: Refine -> Relation -> Expr -> Doc
mkColumn' r rel e = vcat $ punctuate comma 
                    $ map (\e' -> colName e' <+> (mkScalarType $ exprType' r (CtxRelKey rel) e')) 
                    $ e2cols r rel e
    
colName :: Expr -> Doc
colName = pp . replace "." "$" . render . pp

e2cols :: Refine -> Relation -> Expr -> [Expr]
e2cols r rel e = case exprType' r (CtxRelKey rel) e of
                      TStruct _ [c] -> concatMap (e2cols r rel . eField e . name) $ structFields [c]
                      TStruct _ cs  -> e : (concatMap (e2cols r rel . eField e . name) $ structFields cs)
                      _             -> [e]

mkScalarType :: Type -> Doc
mkScalarType (TStruct _ cs)         = mkScalarType $ tBit $ bitWidth $ length cs - 1
mkScalarType (TBool _)              = pp "boolean"
mkScalarType (TString _)            = pp "text"
mkScalarType (TBit _ w) | w < 16    = pp "smallint"
                        | w < 32    = pp "int"
                        | w < 64    = pp "bigint"
                        | otherwise = pp "bit" <> (parens $ pp w)
mkScalarType t                      = error $ "SQL.mkScalarType " ++ show t

defVal :: Type -> Expr
defVal (TStruct _ cs) = defVal $ tBit $ bitWidth $ length cs - 1
defVal (TBool _)      = eBool False
defVal (TString _)    = eString ""
defVal (TBit _ w)     = eBit w 0
defVal t              = error $ "SQL.defVal " ++ show t

mkVal :: Expr -> Doc
mkVal (E (EBool _ True))  = pp "true"
mkVal (E (EBool _ False)) = pp "false"
mkVal (E (EString _ str)) = pp $ show str
mkVal (E (EBit _ w v)) | w < 64    = pp v
                       | otherwise = pp $ "B'" ++ (map ((\b -> if' b '1' '0') . testBit v) [0..w-1]) ++ "'"
mkVal e                   = error $ "SQL.mkVal " ++ show e

mkConstraint :: Refine -> Relation -> Constraint -> Doc
mkConstraint r rel (PrimaryKey _ fs)           = pp "primary key" <+> 
                                                 (parens $ hsep $ punctuate comma $ concatMap (map colName . e2cols r rel) fs)
mkConstraint r rel (ForeignKey _ fs rname fs') = let rel' = getRelation r CtxRefine rname in
                                                 pp "foreign key" <+> 
                                                 (parens $ hsep $ punctuate comma $ concatMap (map colName . e2cols r rel) fs) <+>
                                                 pp "references" <+> 
                                                 (pp rname <+> (parens $ hsep $ punctuate comma $ concatMap (map colName . e2cols r rel') fs'))
mkConstraint r rel (Unique _ fs)               = pp "create unique index on" <+> (pp $ name rel) <+>
                                                 (parens $ hsep $ punctuate comma 
                                                  $ map (\e -> pp "coalesce" <> (parens $ colName e <> comma <+> 
                                                                                       (mkVal $ defVal $ exprType' r (CtxRelKey rel) e)))
                                                  $ concatMap (e2cols r rel) fs)
mkConstraint _ _   (Check _ _)                 = error "mkConstraint check is undefined"

-- primary key: 
-- Validate: 
--      fields always exist (regardless of constructors)
-- mkConstraint:
--      generate condition when fields exist
-- Generate
