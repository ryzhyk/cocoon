{-# LANGUAGE ImplicitParams #-}

-- Convert NetKAT+ spec to P4

module P4.P4( FMap, KMap, PMap
            , genP4Switch) where

import Control.Monad.State
import Text.PrettyPrint
import Data.Bits
import Data.List
import Data.Maybe
import qualified Data.Map as M
import Debug.Trace

import Util
import PP
import Syntax
import Pos
import Type
import NS
import Name


-- State maintained during compilation
data P4State = P4State { p4TableCnt :: Int   -- table counter
                       , p4Tables   :: [Doc] -- table specifications
                       , p4Commands :: [Doc] -- commands to go to the command file
                       }

data P4Statement = P4SSeq   P4Statement P4Statement
                 | P4SITE   Expr P4Statement (Maybe P4Statement)
                 | P4SApply String
                 | P4SDrop

isITE :: P4Statement -> Bool
isITE (P4SITE _ _ _) = True
isITE _              = False

-- Function map: stores values of constant functions
type FMap = M.Map String Expr

-- Key map: maps keys into their values
type KMap = M.Map String Expr

-- Port map: stores physical port range for each input and output port of the switch
type PMap = M.Map String (Integer,Integer)

egressSpec  = EField nopos (EKey nopos "standard_metadata") "egress_spec"
ingressPort = EField nopos (EKey nopos "standard_metadata") "ingress_port"

instance PP P4Statement where
    pp (P4SSeq s1 s2) = (pp s1 <> semi) $$ pp s2
    pp (P4SITE c t e) = pp "if" <+> (parens $ printExpr c) <+> lbrace 
                        $$
                        (nest' $ pp t)
                        $$
                        maybe empty (\st -> (rbrace <+> pp "else" <+> (if' (isITE st) empty lbrace)) 
                                            $$ (nest' $ pp st <> semi)
                                            $$ (if' (isITE st) empty rbrace)) e
    pp (P4SApply n)   = pp "apply" <> (parens $ pp n)
    pp (P4SDrop)      = pp "drop"

data P4Action = P4AModify Expr Expr

instance PP P4Action where
    pp (P4AModify lhs rhs) = pp "modify_field" <> (parens $ printExpr lhs <> comma <+> printExpr rhs)

-- We don't use a separate type for P4 exprressions for now, 
-- just represent them as Expr
printExpr :: Expr -> Doc
printExpr (EKey _ k)        = pp k
printExpr (EPacket _)       = pp "pkt"
printExpr (EField _ e f)    = printExpr e <> char '.' <> pp f
printExpr (EBool _ True)    = pp "true"
printExpr (EBool _ False)   = pp "false"
printExpr (EInt _ v)        = pp $ show v
printExpr (EBinOp _ op l r) = parens $ (printExpr l) <+> printBOp op <+> (printExpr r)
printExpr (EUnOp _ op e)    = parens $ printUOp op <+> printExpr e

printBOp :: BOp -> Doc
printBOp Eq    = pp "=="
printBOp Lt    = pp "<"
printBOp Gt    = pp ">"
printBOp Lte   = pp "<="
printBOp Gte   = pp ">="
printBOp And   = pp "and"
printBOp Or    = pp "or"
printBOp Plus  = pp "+"
printBOp Minus = pp "-"
printBOp Mod   = pp "%"

printUOp :: UOp -> Doc
printUOp Not   = pp "not"

incTableCnt :: State P4State Int
incTableCnt = do
    n <- gets p4TableCnt
    modify (\s -> s{p4TableCnt = n + 1})
    return n

--  Generate P4 switch. Returns to strings: one containing the P4 description
--  of the switch, and one containing runtime commands to initialize switch tables.
genP4Switch :: Refine -> Switch -> FMap -> KMap -> PMap -> (Doc, Doc)
genP4Switch r switch fmap kmap pmap = 
    let ?r = r in
    let ?fmap = fmap in
    let ?pmap = pmap in
    let (controlstat, P4State _ tables commands) = runState (mkSwitch kmap switch) (P4State 0 [] []) 
        control = (pp "control" <+> pp "ingress" <+> lbrace)
                  $$
                  (nest' $ pp controlstat)
                  $$
                  rbrace
    in (pp "#include <parse.p4>" $$ pp "" $$ vcat tables $$ pp "" $$ control, vcat commands)

mkSwitch :: (?r::Refine, ?fmap::FMap, ?pmap::PMap) => KMap -> Switch -> State P4State P4Statement
mkSwitch kmap switch = do
    -- get the list of port numbers for each port group
    let portranges = map (\(port,_) -> trace ("port: " ++ port) $ ?pmap M.! port) $ swPorts switch
    stats <- mapM (\(port,_) -> let ?role = getRole ?r port in 
                                let (first, _) = ?pmap M.! port in
                                let ?kmap = M.insert (name $ last $ roleKeys ?role) (EBinOp nopos Minus ingressPort (EInt nopos first)) kmap in 
                                mkStatement (roleBody ?role))
             $ swPorts switch
    let groups = zip stats portranges
    -- If there are multiple port groups, generate a top-level switch
    return $ foldl' (\st (st', (first, last)) -> let bound1 = EBinOp nopos Gte ingressPort (EInt nopos first)
                                                     bound2 = EBinOp nopos Lte ingressPort (EInt nopos last)
                                                     cond = EBinOp nopos And bound1 bound2
                                                 in P4SITE cond st' (Just st)) 
                    (fst $ head groups) (tail groups)

mkStatement :: (?r::Refine, ?role::Role, ?fmap::FMap, ?kmap::KMap, ?pmap::PMap) => Statement -> State P4State P4Statement
mkStatement (SSeq  _ s1 s2) = do 
    s1' <- mkStatement s1
    s2' <- mkStatement s2
    return $ P4SSeq s1' s2'

mkStatement (SPar  _ _ _)   = error "Not implemented: P4.mkStatement: SPar"

mkStatement (SITE  _ c t e) = do
    let c' = evalExpr c
    t' <- mkStatement t
    e' <- mkStatement e
    return $ P4SITE c' t' (Just e')

mkStatement (STest _ e)     = do
    let e' = evalExpr e
    return $ P4SITE (EUnOp nopos Not e') P4SDrop Nothing

mkStatement (SSet  _ lhs rhs) = do
    tableid <- incTableCnt
    let tablename = "set" ++ show tableid
        lhs' = evalExpr lhs
        rhs' = evalExpr rhs
    mkSingleActionTable tablename (P4AModify lhs' rhs')
    return $ P4SApply tablename

mkStatement (SSend _ (ELocation _ n ks)) = do
    let (base, _) = ?pmap M.! n
        portnum = evalExpr $ EBinOp nopos Plus (EInt nopos base) (last ks) 
    tableid <- incTableCnt
    let tablename = "send" ++ show tableid
    mkSingleActionTable tablename (P4AModify egressSpec portnum)
    return $ P4SApply tablename

mkSingleActionTable :: String -> P4Action -> State P4State ()
mkSingleActionTable n a = do
    let actname = "a_" ++ n
        table = (pp "action" <+> pp actname <> parens empty <+> lbrace)
                $$
                (nest' $ pp a)
                $$
                rbrace
                $$
                (pp "table" <+> pp n <+> lbrace) 
                $$
                (nest' $ pp "actions" <+> (braces $ pp actname))
                $$
                rbrace
        command = pp "table_set_default" <+> pp n <+> pp actname
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [table]
                     , p4Commands = p4Commands p4 ++ [command]})
 

-- Partially evaluate expression
evalExpr  :: (?r::Refine, ?role::Role, ?fmap::FMap, ?kmap::KMap, ?pmap::PMap) => Expr -> Expr
evalExpr (EKey _ k)                    = ?kmap M.! k
evalExpr (EApply _ f [])               = ?fmap M.! f
evalExpr e@(EField _ s f)        = 
    case evalExpr s of
         EStruct _ _ fs -> let (TStruct _ sfs) = typ' ?r ?role s
                               fidx = fromJust $ findIndex ((== f) . name) sfs
                           in fs !! fidx
         s'             -> EField nopos s' f
evalExpr (ELocation _ r ks)            = ELocation nopos r $ map evalExpr ks
evalExpr (EStruct _ s fs)              = EStruct nopos s $ map evalExpr fs
evalExpr (EBinOp _ op lhs rhs)         = 
    let lhs' = evalExpr lhs
        rhs' = evalExpr rhs
        TUInt _ w1 = typ' ?r ?role lhs'
        TUInt _ w2 = typ' ?r ?role rhs'
        w = max w1 w2
    in case (lhs', rhs') of
            (EBool _ v1, EBool _ v2) -> case op of
                                             Eq  -> EBool nopos (v1 == v2)
                                             And -> EBool nopos (v1 && v2)
                                             Or  -> EBool nopos (v1 || v2)
            (EInt _ v1, EInt _ v2)   -> case op of
                                             Eq    -> EBool nopos (v1 == v2)
                                             Lt    -> EBool nopos (v1 < v2)
                                             Gt    -> EBool nopos (v1 > v2)
                                             Lte   -> EBool nopos (v1 <= v2)
                                             Gte   -> EBool nopos (v1 >= v2)
                                             Plus  -> EInt  nopos ((v1 + v2) `mod` (1 `shiftL` w))
                                             Minus -> EInt  nopos ((v1 - v2) `mod` (1 `shiftL` w))
                                             Mod   -> EInt  nopos (v1 `mod` v2)
            _                        -> EBinOp nopos op lhs' rhs'
evalExpr (EUnOp _ op e)                = 
    let e' = evalExpr e
    in case e' of
           (EBool _ v) -> case op of
                               Not -> EBool nopos (not v)
           _           -> EUnOp nopos op e'
evalExpr (ECond _ cs d)                = 
    let cs' = map (\(e1,e2) -> (evalExpr e1, evalExpr e2)) cs
        cs'' = filter ((/= EBool nopos False) . fst) cs'
        d'  = evalExpr d
    in if null cs'' 
          then d'
          else if (fst $ head cs'') == (EBool nopos True)
                  then snd $ head cs''
                  else ECond nopos cs'' d'
evalExpr e                             = e
