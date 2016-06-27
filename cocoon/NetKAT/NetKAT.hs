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
-- NetKAT backend
module NetKAT() where

data NKExpr = NKBool  Bool
            | NKInt   Integer
            | NKVar   String
            | NKEq    NKExpr NKExpr
            | NKAnd   NKExpr NKExpr
            | NKOr    NKExpr NKExpr
            | NKNot   NKExpr

data NKStatement = NKTest NKExpr
                 | NKSet  NKExpr NKExpr
                 | NKSeq  NKStatement NKStatement
                 | NKPar  NKStatement NKStatement

mkSwitch :: Refine -> String -> Store -> Store -> Store -> Doc
mkSwitch r rname fstore kstore pstore = 
    -- If there are multiple port groups, generate a top-level switch

mkPortGroup :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Role -> Doc
mkPortGroup prole = 
    let ?role = prole in mkStatement (roleBody prole)

mkStatement :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Statement -> Doc
mkStatement st = pp $ nkstatSimplify $ mkStatement' st

mkStatement' :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Statement -> NKStatement
mkStatement' st=
    case st of
         SSeq  _ s1 s2   -> NKSeq (mkStatement' s1) (mkStatement' s2)
         SPar  _ s1 s2   -> NKPar (mkStatement' s1) (mkStatement' s2)
         STest _ e       -> NKTest $ mkExpr e
         SSet  _ lhs rhs -> NKSet (mkExpr lhs) (mkExpr rhs)
         SSend _ e       -> NKSet (NKVar "pt") (mkExpr e)

mkExpr :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Expr -> NKExpr
mkExpr 

mkExpr' :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Expr -> Either NKExpr Store
mkExpr' (EKey _ k)      = Right $ storeGet kstore k
mkExpr' (EPacket _)     = error "mkExpr' EPacket"
mkExpr' (EApply _ f []) = Right $ storeGet fstore f
mkExpr' (EField _ e f)  = case mkExpr' e of
                               Left e' -> 
                               Right s -> case storeGet s f of
                                               SVal v -> mkVal v
                                               _      -> 
          | EStruct   {exprPos :: Pos, exprStructName :: String, exprFields :: [Expr]}
          | ELocation {exprPos :: Pos, exprRole :: String, exprArgs :: [Expr]}
          | EBool     {exprPos :: Pos, exprBVal :: Bool}
          | EInt      {exprPos :: Pos, exprIVal :: Integer}
          | EBinOp    {exprPos :: Pos, exprBOp :: BOp, exprLeft :: Expr, exprRight :: Expr}
          | EUnOp     {exprPos :: Pos, exprUOp :: UOp, exprOp :: Expr}
          | ECond     {exprPos :: Pos, exprCases :: [(Expr, Expr)], exprDefault :: Expr}
