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
-- Generic interface of an SMT solver

{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module SMT.SMTSolver where

import qualified Data.Map as M
import Data.Maybe
import Data.List
import GHC.Exts
import Text.PrettyPrint

import PP
import Ops
import Name

maxSolutions :: Int
maxSolutions = 1000

data Type = TBool
          | TInt
          | TString
          | TBit Int
          | TStruct String
          | TArray Type Int
          deriving (Eq)

instance Show Type where
    show TBool        = "bool"
    show (TBit w)     = "bit<" ++ show w ++ ">"
    show TInt         = "int"
    show TString      = "string"
    show (TStruct n)  = n
    show (TArray t l) = "[" ++ show t ++ "; " ++ show l ++ "]"

data Constructor = Constructor { consName :: String 
                               , consArgs :: [Var]
                               } deriving (Eq)

instance WithName Constructor where
    name = consName

data Struct = Struct { structName   :: String 
                     , structCons   :: [Constructor]
                     }

instance WithName Struct where
    name (Struct n _) = n


fieldConstructors :: Struct -> String -> [Constructor]
fieldConstructors s f = filter (any ((== f) . name) . consArgs) $ structCons s

data Var = Var { varName :: String
               , varType :: Type} 
               deriving (Show, Eq)


instance WithName Var where
    name (Var n _) = n


data Function = Function { funcName :: String
                         , funcArgs :: [(String, Type)]
                         , funcType :: Type
                         , funcDef  :: Expr
                         }

instance WithName Function where
    name = funcName

data Expr = EVar        String
          | EApply      String [Expr]
          | EField      String Expr String
          | EBool       Bool
          | EBit        Int Integer
          | EInt        Integer
          | EString     String
          | EStruct     String [Expr]
          | EIsInstance String Expr
          | EBinOp      BOp Expr Expr
          | EUnOp       UOp Expr 
          | ESlice      Expr Int Int
          | ECond       [(Expr, Expr)] Expr
          | ERelPred    String [Expr]
          deriving (Eq)


instance PP Expr where
    pp (EVar v)          = pp v
    pp (EApply f as)     = pp f <> (parens $ hsep $ punctuate comma $ map pp as)
    pp (EField _ s f)    = pp s <> "." <> pp f
    pp (EBool True)      = "true"
    pp (EBool False)     = "false"
    pp (EBit w v)        = pp w <> "'d" <> pp v
    pp (EInt i)          = pp i
    pp (EString s)       = "\"" <> pp s <> "\""
    pp (EStruct c as)    = pp c <> "{" <> (hsep $ punctuate comma $ map pp as)  <> "}"
    pp (EIsInstance c e) = "is_" <> pp c <> parens (pp e)
    pp (EBinOp op l r)   = parens $ pp l <+> pp op <+> pp r
    pp (EUnOp op e)      = parens $ pp op <+> pp e 
    pp (ESlice e h l)    = pp e <> "[" <> pp h <> ":" <> pp l <> "]" 
    pp (ECond cs d)      = "case {" <>
                           (nest' $ (hsep $ map (\(c,e) -> pp c <> ":" <+> pp e <> comma) cs) <+> "default:" <+> pp d) <>
                           "}"
    pp (ERelPred p as)   = pp p <> (parens $ hsep $ punctuate comma $ map pp as)

instance Show Expr where
    show = render . pp

(#==) e1 e2 = EBinOp Eq     e1 e2
(#/=) e1 e2 = EBinOp Neq    e1 e2
(#<)  e1 e2 = EBinOp Lt     e1 e2
(#>)  e1 e2 = EBinOp Gt     e1 e2
(#<=) e1 e2 = EBinOp Lte    e1 e2
(#>=) e1 e2 = EBinOp Gte    e1 e2
(#&&) e1 e2 = EBinOp And    e1 e2
(#||) e1 e2 = EBinOp Or     e1 e2
(#=>) e1 e2 = EBinOp Impl   e1 e2
(#+)  e1 e2 = EBinOp Plus   e1 e2
(#-)  e1 e2 = EBinOp Minus  e1 e2
(#%)  e1 e2 = EBinOp Mod    e1 e2
(#>>) e1 e2 = EBinOp ShiftR e1 e2
(#<<) e1 e2 = EBinOp ShiftL e1 e2
(#++) e1 e2 = EBinOp Concat e1 e2

exprMap :: (Expr -> Expr) -> Expr -> Expr
exprMap g e@(EVar _)          = g e
exprMap g   (EApply f as)     = g $ EApply f $ map (exprMap g) as
exprMap g   (EField c s f)    = g $ EField c (exprMap g s) f
exprMap g e@(EBool _)         = g e
exprMap g e@(EBit _ _)        = g e
exprMap g e@(EInt _)          = g e
exprMap g e@(EString _)       = g e
exprMap g   (EStruct c fs)    = g $ EStruct c $ map (exprMap g) fs
exprMap g   (EIsInstance c e) = g $ EIsInstance c $ exprMap g e
exprMap g   (EBinOp op e1 e2) = g $ EBinOp op (exprMap g e1) (exprMap g e2)
exprMap g   (EUnOp op e1)     = g $ EUnOp op $ exprMap g e1
exprMap g   (ESlice e1 h l)   = g $ ESlice (exprMap g e1) h l
exprMap g   (ECond cs d)      = g $ ECond (map (\(e1,e2) -> (exprMap g e1, exprMap g e2)) cs) $ exprMap g d
exprMap g   (ERelPred r as)   = g $ ERelPred r $ map (exprMap g) as

exprCollect :: (Expr -> [a]) -> Expr -> [a]
exprCollect f e@(EApply _ as)     = (concatMap (exprCollect f) as) ++ f e
exprCollect f e@(EField _ s _)    = (exprCollect f s) ++ f e
exprCollect f e@(EStruct _ as)    = (concatMap (exprCollect f) as) ++ f e
exprCollect f e@(EIsInstance _ a) = (exprCollect f a) ++ f e
exprCollect f e@(EBinOp _ e1 e2)  = (exprCollect f e1) ++ (exprCollect f e2) ++ f e
exprCollect f e@(EUnOp _ a)       = (exprCollect f a) ++ f e
exprCollect f e@(ESlice a _ _)    = (exprCollect f a) ++ f e
exprCollect f e@(ECond cs d)      = (concatMap (\(c,v) -> exprCollect f c ++ exprCollect f v) cs) ++ exprCollect f d ++ f e
exprCollect f e@(ERelPred _ as)   = (concatMap (exprCollect f) as) ++ f e
exprCollect f e                   = f e

exprVars :: Expr -> [String]
exprVars e = nub $ exprCollect (\case 
                                 EVar v -> [v]
                                 _      -> []) e

conj :: [Expr] -> Expr
conj = conj' . filter (/= EBool True)

conj' :: [Expr] -> Expr
conj' []     = EBool True
conj' [e]    = e
conj' (e:es) = EBinOp And e (conj' es)

disj :: [Expr] -> Expr
disj = disj' . filter (/= EBool False)

disj' :: [Expr] -> Expr
disj' []     = EBool False
disj' [e]    = e
disj' (e:es) = EBinOp Or e (disj' es)


-- Assigns values to variables.
type Assignment = M.Map String Expr

typ :: SMTQuery -> Maybe Function -> Expr -> Type
typ q mf (EVar n)          = maybe (varType $ fromJust $ find ((==n) . name) $ smtVars q)
                                   (snd . fromJust . find ((==n) . fst) . funcArgs)
                                   mf
typ q _  (EField c _ f)    = varType $ fromJust $ find ((==f) . name) $ concatMap consArgs cs
                             where Struct _ cs = getConsStruct q c
typ _ _  (EBool _)         = TBool
typ _ _  (EBit w _)        = TBit w
typ _ _  (EInt _)          = TInt
typ _ _  (EString _)       = TString
typ q _  (EStruct c _)     = TStruct $ structName $ getConsStruct q c
typ _ _  (EIsInstance _ _) = TBool
typ q mf (EBinOp op e1 _)  | elem op [Eq, Lt, Gt, Lte, Gte, And, Or] = TBool
                           | elem op [Plus, Minus, Mod] = typ q mf e1
typ _ _  (EUnOp Not _)     = TBool 
typ _ _  (ESlice _ h l)    = TBit (h-l+1)
typ q mf (ECond _ d)       = typ q mf d
typ q _  (EApply f _)      = funcType $ fromJust $ find ((==f) . name) $ smtFuncs q
typ _ _  (ERelPred _ _)    = TBool 
typ _ _  e                 = error $ "SMTSolver.typ " ++ show e

data SMTQuery = SMTQuery { smtStructs :: [Struct]
                         , smtVars    :: [Var]
                         , smtFuncs   :: [Function]
                         , smtHard    :: [Expr]
                         , smtSoft    :: [(Expr, Int)]
                         }

lookupConsStruct :: SMTQuery -> String -> Maybe Struct
lookupConsStruct q c = find (isJust . find ((==c) . name) . structCons) $ smtStructs q

getConsStruct :: SMTQuery -> String -> Struct
getConsStruct q c = fromJust $ lookupConsStruct q c

getConstructor :: SMTQuery -> String -> Constructor
getConstructor q c = head $ concatMap (filter ((==c) . name) . structCons) $ smtStructs q

data SMTSolver = SMTSolver {
    -- Input:  list of formula
    -- Output: Nothing    - satisfiability of the formula could not be established
    --         Just Left  - unsat core of the conjunction of formula
    --         Just Right - satisfying assignment (unassigned variables are don't cares)
    smtGetModel       :: SMTQuery -> Maybe (Maybe Assignment),
    smtCheckSAT       :: SMTQuery -> Maybe Bool,
    smtGetCore        :: SMTQuery -> Maybe (Maybe [Int]),
    smtGetModelOrCore :: SMTQuery -> Maybe (Either [Int] Assignment)
}


allValues :: SMTQuery -> Type -> [Expr]
allValues _ TBool       = [EBool True, EBool False]
allValues _ (TBit w)    = map (EBit w) [0..2^w-1]
allValues q (TStruct n) = concatMap (map (EStruct n) . allvals . consArgs) cs
    where Struct _ cs = fromJust $ find ((==n) . name) $ smtStructs q
          allvals []          = [[]]
          allvals (f:fs') = concatMap (\v -> map (v:) $ allvals fs') $ allValues q $ varType f
allValues _ t           = error $ "Not implemented SMTSolver.allValues " ++ show t

allSolutionsVar :: SMTSolver -> SMTQuery -> String -> [Expr]
allSolutionsVar solver q var = sortWith solToArray $ allSolutionsVar' solver q var

allSolutionsVar' :: SMTSolver -> SMTQuery -> String -> [Expr]
allSolutionsVar' solver q var = 
    -- Find one solution; block it, call allSolutionsVar' recursively to find more
    case smtGetModel solver q of
         Nothing           -> error "SMTSolver.allSolutionsVar: Failed to solve SMT query"
         Just Nothing      -> []
         Just (Just model) -> case M.lookup var model of
                                   Nothing  -> allValues q $ typ q Nothing $ EVar var
                                   Just val -> let q' = q{smtHard = (EUnOp Not $ EBinOp Eq (EVar var) val) : (smtHard q)}
                                               in val:(allSolutionsVar' solver q' var)

solToArray :: Expr -> [Integer]
solToArray (EBool True)   = [1]
solToArray (EBool False)  = [0]
solToArray (EBit _ i)     = [i]
solToArray (EStruct _ es) = concatMap solToArray es
solToArray e              = error $ "SMTSolver.solToArray " ++ show e


allSolutions :: SMTSolver -> SMTQuery -> [Assignment]
allSolutions solver q = allSolutions' 0 solver q

allSolutions' :: Int -> SMTSolver -> SMTQuery -> [Assignment]
allSolutions' nfound solver q = 
    if nfound > maxSolutions
       then error $ "SMTSolver.allSolutions: " ++ show nfound ++ " solutions found.  Aborting enumeration." 
       else -- Find one solution; block it, call allSolutions' recursively to find more
            case smtGetModel solver q of
                 Nothing           -> error "SMTSolver.allSolutions: Failed to solve SMT query"
                 Just Nothing      -> []
                 Just (Just model) -> let emodel = foldl' (\a (v,e) -> EBinOp And a (EBinOp Eq (EVar v) e)) (EBool True) $ M.toList model
                                          q' = q{smtHard = (EUnOp Not emodel) : (smtHard q)}
                                      in model : allSolutions' (nfound + 1) solver q'

