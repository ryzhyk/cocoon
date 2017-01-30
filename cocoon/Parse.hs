{-# LANGUAGE FlexibleContexts #-}

module Parse ( cocoonGrammar
             , cfgGrammar) where

import Control.Applicative hiding (many,optional,Const)
import Control.Monad
import Text.Parsec hiding ((<|>))
import Text.Parsec.Expr
import Text.Parsec.Language
import qualified Text.Parsec.Token as T
import Data.Maybe
import Data.Either
import Numeric

import Syntax
import Pos
import Util

reservedOpNames = ["?", "!", "|", "==", "=", ":=", ":-", "%", "+", "-", ".", "=>", "<=", "<=>", ">=", "<", ">", "!=", ">>", "<<", "_"]
reservedNames = ["and",
                 "assume",
                 "bit",
                 "bool",
                 "check",
                 "constraint",
                 "default",
                 "else",
                 "false",
                 "filter",
                 "foreign",
                 "fork",
                 "function",
                 "host",
                 "havoc",
                 "if",
                 "int",
                 "key",
                 "let",
                 "sink",
                 "not",
                 "or",
                 "pkt",
                 "primary",
                 "references",
                 "refine",
                 "role",
                 "send",
                 "string",
                 "switch",
                 "table",
                 "true",
                 "typedef",
                 "unique",
                 "view"]


lexer = T.makeTokenParser (emptyDef {T.commentStart      = "/*"
                                    ,T.commentEnd        = "*/"
                                    ,T.commentLine       = "//"
                                    ,T.nestedComments    = True
                                    ,T.identStart        = letter <|> char '_' 
                                    ,T.identLetter       = alphaNum <|> char '_'
                                    ,T.reservedOpNames   = reservedOpNames
                                    ,T.reservedNames     = reservedNames
                                    ,T.opLetter          = oneOf "_!?:%*-+./=|<>"
                                    ,T.caseSensitive     = True})


reservedOp = T.reservedOp lexer
reserved   = T.reserved lexer
identifier = T.identifier lexer
--semiSep    = T.semiSep lexer
--semiSep1   = T.semiSep1 lexer
colon      = T.colon lexer
commaSep   = T.commaSep lexer
commaSep1  = T.commaSep1 lexer
symbol     = T.symbol lexer
semi       = T.semi lexer
comma      = T.comma lexer
braces     = T.braces lexer
parens     = T.parens lexer
angles     = T.angles lexer
brackets   = T.brackets lexer
natural    = T.natural lexer
decimal    = T.decimal lexer
--integer    = T.integer lexer
whiteSpace = T.whiteSpace lexer
lexeme     = T.lexeme lexer
dot        = T.dot lexer
stringLit  = T.stringLiteral lexer
--charLit    = T.charLiteral lexer


removeTabs = do s <- getInput
                let s' = map (\c -> if c == '\t' then ' ' else c ) s 
                setInput s'          

withPos x = (\s a e -> atPos a (s,e)) <$> getPosition <*> x <*> getPosition


data SpecItem = SpType         TypeDef
              | SpRelation     Relation
              | SpAssume       Assume
              | SpFunc         Function
              | SpRole         Role
              | SpNode         Node


cocoonGrammar = Spec <$ removeTabs <*> ((optional whiteSpace) *> spec <* eof)
cfgGrammar = removeTabs *> ((optional whiteSpace) *> (many relation) <* eof)

spec = (\r rs -> r:rs) <$> (withPos $ mkRefine [] <$> (many decl)) <*> (many refine)

mkRefine :: [String] -> [SpecItem] -> Refine
mkRefine targets items = Refine nopos targets types funcs relations assumes roles nodes
    where types = mapMaybe (\i -> case i of 
                                       SpType t -> Just t
                                       _        -> Nothing) items
          funcs = mapMaybe (\i -> case i of 
                                       SpFunc f -> Just f
                                       _        -> Nothing) items
          roles = mapMaybe (\i -> case i of 
                                       SpRole r -> Just r
                                       _        -> Nothing) items
          relations = mapMaybe (\i -> case i of 
                                           SpRelation r -> Just r
                                           _            -> Nothing) items
          assumes = mapMaybe (\i -> case i of 
                                       SpAssume a -> Just a
                                       _          -> Nothing) items
          nodes = mapMaybe (\i -> case i of 
                                       SpNode n -> Just n
                                       _        -> Nothing) items

refine = withPos $ mkRefine <$  reserved "refine" 
                            <*> (commaSep identifier)
                            <*> (braces $ many decl)

decl =  (SpType         <$> typeDef)
    <|> (SpFunc         <$> func)
    <|> (SpRole         <$> role)
    <|> (SpRelation     <$> relation)
    <|> (SpAssume       <$> assume)
    <|> (SpNode         <$> node)


typeDef = withPos $ (TypeDef nopos) <$ reserved "typedef" <*> identifier <*> (reservedOp "=" *> typeSpec)

func = withPos $ Function nopos <$  reserved "function" 
                                <*> identifier 
                                <*> (parens $ commaSep arg) 
                                <*> (colon *> (Just <$> typeSpecSimple) <|> (Nothing <$ reserved "sink"))
                                <*> (option (EBool nopos True) (reservedOp "|" *> expr))
                                <*> (reservedOp "=" *> expr)

relation = withPos $ do reserved "table" 
                        n <- identifier
                        (as, cs) <- liftM partitionEithers $ parens $ commaSep argOrConstraint
                        return $ Relation nopos n as cs Nothing
                 <|> do reserved "view" 
                        n <- identifier
                        (as, cs) <- liftM partitionEithers $ parens $ commaSep argOrConstraint
                        rs <- many1 $ withPos $ do 
                                      try $ lookAhead $ identifier *> (parens $ commaSep expr) *> reservedOp ":-"
                                      rn <- identifier
                                      when (rn /= n) $ fail $ "Only rules for relation \"" ++ n ++ "\" can be defined here"
                                      rargs <- parens $ commaSep expr
                                      reservedOp ":-"
                                      rhs <- commaSep expr
                                      return $ Rule nopos rargs rhs
                        return $ Relation nopos n as cs $ Just rs

argOrConstraint =  (Right <$> constraint)
               <|> (Left  <$> arg)

constraint = withPos $  (PrimaryKey nopos <$ reserved "primary" <*> (reserved "key" *> (parens $ commaSep identifier)))
                    <|> (ForeignKey nopos <$ reserved "foreign" <*> (reserved "key" *> (parens $ commaSep expr)) 
                                          <*> (reserved "references" *> identifier) <*> (parens $ commaSep identifier))
                    <|> (Unique     nopos <$ reserved "unique" <*> (parens $ commaSep expr))
                    <|> (Check      nopos <$ reserved "check" <*> expr)


role = withPos $ Role nopos <$  reserved "role" 
                            <*> identifier 
                            <*> (brackets $ commaSep arg) 
                            <*> (option (EBool nopos True) (reservedOp "|" *> expr))
                            <*> (option (EBool nopos True) (reservedOp "/" *> expr))
                            <*> (reservedOp "=" *> expr)

assume = withPos $ Assume nopos <$ reserved "assume" <*> (option [] $ parens $ commaSep arg) <*> expr

node = withPos $ Node nopos <$> ((NodeSwitch <$ reserved "switch") <|> (NodeHost <$ reserved "host"))
                            <*> identifier 
                            <*> (parens $ commaSep1 $ parens $ (,) <$> identifier <* comma <*> identifier)

arg = withPos $ (Field nopos) <$> identifier <*> (colon *> typeSpecSimple)

typeSpec = withPos $ 
            arrType
        <|> bitType 
        <|> intType
        <|> stringType
        <|> boolType 
        <|> userType 
        <|> structType 
        <|> tupleType
        
typeSpecSimple = withPos $ 
                  arrType
              <|> bitType 
              <|> intType
              <|> stringType
              <|> boolType 
              <|> tupleType
              <|> userType 

bitType    = TBit    nopos <$ reserved "bit" <*> (fromIntegral <$> angles decimal)
intType    = TInt    nopos <$ reserved "int"
stringType = TString nopos <$ reserved "string"
boolType   = TBool   nopos <$ reserved "bool"
userType   = TUser   nopos <$> identifier
arrType    = brackets $ TArray nopos <$> typeSpecSimple <* semi <*> (fromIntegral <$> decimal)
structType = TStruct nopos <$ isstruct <*> sepBy1 constructor (reservedOp "|") 
    where isstruct = try $ lookAhead $ identifier *> symbol "{"
tupleType  = TTuple  nopos <$> (parens $ commaSep typeSpecSimple)

constructor = withPos $ Constructor nopos <$> identifier <*> (option [] $ braces $ commaSep arg)

expr =  buildExpressionParser etable term
    <?> "expression"

term  =  parens expr 
     <|> braces expr
     <|> term'
term' = withPos $
         estruct
     <|> ebuiltin
     <|> eapply
     <|> eloc
     <|> eint
     <|> ebool
     <|> estring
     <|> epacket
     <|> evar
     <|> eswitch
     <|> etest
     <|> eite
     <|> esend
     <|> eset
     <|> elet
     <|> endlet
     <|> efork
     <|> epholder

eapply = EApply nopos <$ isapply <*> identifier <*> (parens $ commaSep expr)
    where isapply = try $ lookAhead $ identifier *> symbol "("
ebuiltin = EBuiltin nopos <$ isbuiltin <*> (identifier <* char '!') <*> (parens $ commaSep expr)
    where isbuiltin = try $ lookAhead $ (identifier *> char '!') *> symbol "("
eloc = ELocation nopos <$ isloc <*> identifier <*> (brackets $ commaSep expr)
    where isloc = try $ lookAhead $ identifier *> (brackets $ commaSep expr)
ebool = EBool nopos <$> ((True <$ reserved "true") <|> (False <$ reserved "false"))
epacket = EPacket nopos <$ reserved "pkt"
evar = EVar nopos <$> identifier
eswitch = (fmap uncurry (ESwitch nopos <$ reserved "switch" <*> expr))
               <*> (braces $ (,) <$> (commaSep1 $ (,) <$> expr <* colon <*> expr) 
                                 <*> (optionMaybe $ comma *> reserved "default" *> colon *> expr))
--eint  = EInt nopos <$> (fromIntegral <$> decimal)
eint  = lexeme eint'
estring = EString nopos <$> stringLit
estruct = EStruct nopos <$ isstruct <*> identifier <*> (braces $ commaSep1 expr)
    where isstruct = try $ lookAhead $ identifier *> symbol "{"

eint'   = (lookAhead $ char '\'' <|> digit) *> (do w <- width
                                                   v <- sradval
                                                   mkLit w v)

etest   = ETest   nopos <$ reserved "filter" <*> expr
esend   = ESend   nopos <$ reserved "send" <*> expr
eset    = ESet    nopos <$ isset <*> expr <*> (reservedOp ":=" *> expr)
    where isset = try $ lookAhead $ expr *> reservedOp ":="
eite    = EITE    nopos <$ reserved "if" <*> expr <*> expr <*> (optionMaybe $ reserved "else" *> expr)
elet    = ELet    nopos <$ islet <*> (reserved "let" *> expr) <*> (reservedOp "=" *> expr)
    where islet = try $ lookAhead $ reserved "let" *> expr *> reservedOp "="
endlet  = ENDLet  nopos <$ reserved "let" <*> (commaSep1 identifier) <*> (reservedOp "|" *> expr)
efork   = EFork   nopos <$ reserved "fork" <*> (commaSep1 identifier) <*> (reservedOp "|" *> expr) <*> expr
epholder = EPHolder nopos <$ reservedOp "_"

width = optionMaybe (try $ ((fmap fromIntegral parseDec) <* (lookAhead $ char '\'')))
sradval =  ((try $ string "'b") *> parseBin)
       <|> ((try $ string "'o") *> parseOct)
       <|> ((try $ string "'d") *> parseDec)
       <|> ((try $ string "'h") *> parseHex)
       <|> parseDec
parseBin :: Stream s m Char => ParsecT s u m Integer
parseBin = readBin <$> (many1 $ (char '0') <|> (char '1'))
parseOct :: Stream s m Char => ParsecT s u m Integer
parseOct = (fst . head . readOct) <$> many1 octDigit
parseDec :: Stream s m Char => ParsecT s u m Integer
parseDec = (fst . head . readDec) <$> many1 digit
--parseSDec = (\m v -> m * v)
--            <$> (option 1 ((-1) <$ reservedOp "-"))
--            <*> ((fst . head . readDec) <$> many1 digit)
parseHex :: Stream s m Char => ParsecT s u m Integer
parseHex = (fst . head . readHex) <$> many1 hexDigit

mkLit :: Maybe Int -> Integer -> ParsecT s u m Expr
mkLit Nothing  v                       = return $ EInt nopos v
mkLit (Just w) v | w == 0              = fail "Unsigned literals must have width >0"
                 | msb v < w           = return $ EBit nopos w v
                 | otherwise           = fail "Value exceeds specified width"

etable = [[postf $ choice [postSlice, postField]]
         ,[pref  $ choice [prefix "not" Not]]
         ,[binary "%" Mod AssocLeft]
         ,[binary "+" Plus AssocLeft,
           binary "-" Minus AssocLeft]
         ,[binary ">>" ShiftR AssocLeft,
           binary "<<" ShiftL AssocLeft]
         ,[binary "++" Concat AssocLeft]
         ,[binary "==" Eq  AssocLeft,          
           binary "!=" Neq AssocLeft,          
           binary "<"  Lt  AssocNone, 
           binary "<=" Lte AssocNone, 
           binary ">"  Gt  AssocNone, 
           binary ">=" Gte AssocNone]
         ,[binary "and" And AssocLeft]
         ,[binary "or" Or AssocLeft]
         ,[binary "=>" Impl AssocLeft]
         ,[sbinary ";" ESeq AssocRight]
         ,[sbinary "|" EPar AssocRight]
         ]

pref  p = Prefix  . chainl1 p $ return       (.)
postf p = Postfix . chainl1 p $ return (flip (.))
postField  = (\f end e -> EField (fst $ pos e, end) e f) <$> field <*> getPosition
postSlice  = try $ (\(h,l) end e -> ESlice (fst $ pos e, end) e h l) <$> slice <*> getPosition
slice = brackets $ (\h l -> (fromInteger h, fromInteger l)) <$> natural <*> (colon *> natural)

field = dot *> identifier

prefix n fun = (\start e -> EUnOp (start, snd $ pos e) fun e) <$> getPosition <* reservedOp n
binary n fun  = Infix $ (\le re -> EBinOp (fst $ pos le, snd $ pos re) fun le re) <$ reservedOp n
sbinary n fun = Infix $ (\l  r  -> fun (fst $ pos l, snd $ pos r) l r) <$ reservedOp n


