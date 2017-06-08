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
{-# LANGUAGE ImplicitParams #-}

module SMT.SMTLib2Parse ( assertName
                        , satresParser
                        , unsatcoreParser
                        , modelParser
                        , exprParser
                        , errorParser) where

import Data.Maybe
import Data.List
import qualified Data.Map             as M
import Text.Parsec hiding ((<|>))
import Text.Parsec.Language
import qualified Text.Parsec.Token    as T
import Control.Applicative hiding (many)
import Numeric

import Util
import SMT.SMTSolver
import Ops

-- appended to each assertion name
assertName :: String
assertName = "__assert"

data ModelDecl = DeclConst  String TypeSpec
               | DeclVarAsn String [String] SMTExpr
               deriving (Eq)

declIsAsn :: ModelDecl -> Bool
declIsAsn (DeclVarAsn _ _ _) = True
declIsAsn _                  = False

data TypeSpec = TypeName  String
              | TypeArray TypeSpec TypeSpec                
              | TypeBV    Int
              deriving (Eq)

data SMTExpr = ExpIdent   String
             | ExpBool    Bool
             | ExpInt     Integer
             | ExpApply   String [SMTExpr]
             | ExpAsArray String
             deriving (Eq, Ord, Show)

------------------------------------------------------
-- exports
------------------------------------------------------

satresParser :: Parsec String () Bool
satresParser = (False <$ symbol "unsat") <|> 
               (True  <$ symbol "sat")

unsatcoreParser :: Parsec String () [Int]
unsatcoreParser = option [] (parens $ many $ (string assertName *> (fromInteger <$> decimal)) <* spaces)

modelParser :: (?q::SMTQuery) => Parsec String () Assignment
modelParser = assignmentFromModel <$> model

exprParser :: (?q::SMTQuery) => Maybe Type -> Parsec String () Expr
exprParser t = parseExpr t <$> expr

errorParser = char '(' *> symbol "error" *> (many $ noneOf ['(',')']) <* char ')' <* spaces

------------------------------------------------------
-- Parsing solver output
------------------------------------------------------

reservedNames   = ["model", "declare-fun", "define-fun", "forall", "BitVec", "Array", "true", "false", "as-array"]
reservedOpNames = ["_"]

lexer  = T.makeTokenParser emptyDef { T.identStart      =  letter 
                                                       <|> char '_' 
                                                       <|> char '$'
                                                       <|> char ':'
                                    , T.identLetter     =  alphaNum 
                                                       <|> char '_' 
                                                       <|> char '-' 
                                                       <|> char '!' 
                                                       <|> char '$' 
                                                       <|> char '/'
                                                       <|> char ':'
                                    , T.commentLine     = ";;"
                                    , T.reservedNames   = reservedNames
                                    , T.reservedOpNames = reservedOpNames
                                    }

identifier = T.identifier lexer
symbol     = T.symbol     lexer
decimal    = T.decimal    lexer
parens     = T.parens     lexer
reserved   = T.reserved   lexer
operator   = T.operator   lexer
reservedOp = T.reservedOp lexer
lexeme     = T.lexeme     lexer

ident =  identifier 
     <|> char '|' *> (many $ noneOf ['|']) <* char '|' <* spaces

model = catMaybes <$> (parens $ reserved "model" *> many model_decl)

model_decl :: Parsec String () (Maybe ModelDecl)
model_decl =  try const_decl
          <|> try var_asn
          <|> try forall

const_decl = parens $ (\n t -> Just $ DeclConst n t)    <$ reserved "declare-fun" <*> ident <* (parens spaces) <*> typespec
var_asn    = parens $ (\n as _ e -> if' (isPrefixOf assertName n) Nothing (Just $ DeclVarAsn n as e)) -- ignore assignments to assertions
                                                        <$ reserved "define-fun"  <*> ident <*> args <*> typespec <*> expr
forall     = parens $ (\_ _ -> Nothing)                 <$ reserved "forall"      <*> args  <*> expr

args = parens $ many arg
arg  = parens $ ident <* typespec

expr =  (isarray *> asarray)
    <|> fapply
    <|> literal
    <|> (ExpIdent <$> ident)

asarray = parens $ ExpAsArray <$> (reservedOp "_" *> reserved "as-array" *> ident)
isarray = try $ lookAhead asarray

fapply = parens $ ExpApply <$> fname <*> (many expr)
fname  =  ident 
      <|> operator

typespec =  (parens $  (TypeArray <$ reserved "Array" <*> typespec <*> typespec)
                   <|> ((TypeBV . fromInteger) <$> (reservedOp "_" *> reserved "BitVec" *> decimal)))
        <|> TypeName <$> ident

literal =  (ExpInt <$> decimal)
       <|> (ExpBool True <$ reserved "true")
       <|> (ExpBool False <$ reserved "false")
       <|> (try $ lexeme $ string "#x" *> ((ExpInt . fst . head . readHex) <$> many1 hexDigit))
       <|> (try $ lexeme $ string "#b" *> ((ExpInt . readBin)              <$> (many1 $ char '0' <|> char '1')))

------------------------------------------------------
-- Compiling parsed data
------------------------------------------------------

assignmentFromModel :: (?q::SMTQuery) => [ModelDecl] -> Assignment
assignmentFromModel decls = 
    let asndecls = map (\(DeclVarAsn n _ v) -> (n, v)) $ filter declIsAsn decls in
    M.unions (map parseAsn asndecls)

parseAsn :: (?q::SMTQuery) => (String, SMTExpr) -> Assignment
parseAsn (n, e) = let t = varType $ fromJust $ find ((==n) . varName) $ smtVars ?q
                      val = parseExpr (Just t) e 
                  in M.singleton n val

parseExpr :: (?q::SMTQuery) => Maybe Type -> SMTExpr -> Expr
parseExpr _                 (ExpBool b)                  = EBool b
parseExpr (Just (TBit w))   (ExpInt v)                   = EBit w v
parseExpr _                 (ExpInt v)                   = EInt v
parseExpr _                 (ExpApply ":var" [ExpInt i]) = EVar $ ":var" ++ show i
parseExpr _                 (ExpApply "=" [e1, e2])      = EBinOp Eq (parseExpr Nothing e1) (parseExpr Nothing e2)
parseExpr _                 (ExpApply "or" as)           = disj $ map (parseExpr $ Just TBool) as
parseExpr _                 (ExpApply "and" as)          = conj $ map (parseExpr $ Just TBool) as
parseExpr t                 (ExpApply "ite" [i,th,el])   = if' cond (parseExpr t th) (parseExpr t el)
    where cond = case parseExpr (Just TBool) i of
                      EBool b -> b
                      _       -> error $ "parseExpr: cannot evaluate boolean expression " ++ show i
parseExpr _                 (ExpApply n as) | isJust cons = 
    if length fs /= length as
       then error "SMTLib2Parse.parseExpr: incorrect number of fields in a struct"
       else EStruct n (map (\((_,t), e) -> parseExpr (Just t) e) $ zip fs as)
    where cons = find ((==n) . fst) $ concatMap structCons $ smtStructs ?q
          fs = snd $ fromJust cons

--parseExpr (ExpIdent i) = case lookupEnumerator i of
--         Just _  -> SVal $ EnumVal i
--         Nothing -> case M.lookup i args of
--                         Just e  -> parseExpr t e M.empty
--                         Nothing -> error $ "parseExpr: unknown enumerator: " ++ show i

--parseExpr (Array _ t l) (ExpAsArray n) _ | isNothing marr = error $ "parseExpr: array \"" ++ n ++ "\" not found"
--                                            | otherwise      = SArr $ M.fromList $ map (\i -> (i, parseExpr t e $ M.singleton a (ExpInt $ fromIntegral i))) [0..l-1]
--    where marr = find ((==n) . dvarName) ?alldecls
--          Just (DeclVarAsn _ [a] e) = marr

--parseExpr t (ExpApply "=" [a1,a2]) = SVal $ BoolVal $ v1 == v2
--    where -- XXX: assume that comparisons are always between (integer) array indices
--          SVal (UIntVal _ v1) = parseExpr (UInt Nothing 32) a1
--          SVal (UIntVal _ v2) = parseExpr (UInt Nothing 32) a2
parseExpr t e = error $ "SMTLib2Parse.parseExpr " ++ show t ++ " " ++ show e
