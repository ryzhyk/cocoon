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
-- Generic interface of an SMT solver

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

instance Show Type where
    show TBool        = "bool"
    show (TBit w)     = "bit<" ++ show w ++ ">"
    show TInt         = "int"
    show TString      = "string"
    show (TStruct n)  = n
    show (TArray t l) = "[" ++ show t ++ "; " ++ show l ++ "]"

data Struct = Struct { structName   :: String 
                     , structCons   :: [(String, [(String,Type)])]
                     }

instance WithName Struct where
    name (Struct n _) = n

data Var = Var { varName :: String
               , varType :: Type} 
               deriving Show


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
          deriving (Show, Eq)

instance PP Expr where
    pp = text . show

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
typ q _  (EField c _ f)    = fromJust $ lookup f $ concatMap snd cs
                             where Struct _ cs = smtConstr2Struct q c
typ _ _  (EBool _)         = TBool
typ _ _  (EBit w _)        = TBit w
typ _ _  (EInt _)          = TInt
typ _ _  (EString _)       = TString
typ q _  (EStruct c _)     = TStruct $ structName $ smtConstr2Struct q c
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
                         , smtExprs   :: [Expr]
                         }

smtConstr2Struct :: SMTQuery -> String -> Struct
smtConstr2Struct q c = fromJust $ find (isJust . lookup c . structCons) $ smtStructs q

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
allValues q (TStruct n) = concatMap (map (EStruct n) . allvals . snd) cs
    where Struct _ cs = fromJust $ find ((==n) . name) $ smtStructs q
          allvals []          = [[]]
          allvals ((_,t):fs') = concatMap (\v -> map (v:) $ allvals fs') $ allValues q t
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
                                   Just val -> let q' = q{smtExprs = (EUnOp Not $ EBinOp Eq (EVar var) val) : (smtExprs q)}
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
                                          q' = q{smtExprs = (EUnOp Not emodel) : (smtExprs q)}
                                      in model : allSolutions' (nfound + 1) solver q'

