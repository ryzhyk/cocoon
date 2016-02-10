{-# LANGUAGE ImplicitParams #-}

-- Convert NetKAT+ spec to P4

module P4.P4( genP4Switches
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
import Eval
import Topology
import P4.Header

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

-- Port map: stores physical port range for each input and output port of the switch
type PMap = M.Map String (Int,Int)

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

-- We don't use a separate type for P4 expressions for now, 
-- just represent them as Expr
printExpr :: Expr -> Doc
printExpr (EKey _ k)        = pp k
printExpr (EPacket _)       = pp "pkt"
printExpr (EField _ e f)    = printExpr e <> char '.' <> pp f
printExpr (EBool _ True)    = pp "true"
printExpr (EBool _ False)   = pp "false"
printExpr (EInt _ _ v)      = pp $ show v
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

-- Generate all P4 switches in the topology
genP4Switches :: Refine -> FMap -> Topology -> [(InstanceDescr, (Doc, Doc))]
genP4Switches r fmap topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = M.fromList $ concatMap (\((i,o),range,_) -> [(i,range),(o,range)]) links
                                                          in (descr, genP4Switch r switch fmap kmap pmap)) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology

--  Generate P4 switch. Returns to strings: one containing the P4 description
--  of the switch, and one containing runtime commands to initialize switch tables.
genP4Switch :: Refine -> Node -> FMap -> KMap -> PMap -> (Doc, Doc)
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
    in (pp p4HeaderDecls $$ pp "" $$ vcat tables $$ pp "" $$ control, vcat commands)

mkSwitch :: (?r::Refine, ?fmap::FMap, ?pmap::PMap) => KMap -> Node -> State P4State P4Statement
mkSwitch kmap switch = do
    -- get the list of port numbers for each port group
    let portranges = map (\(port,_) -> ?pmap M.! port) $ nodePorts switch
    stats <- mapM (\(port,_) -> let ?role = getRole ?r port in 
                                let (first, _) = ?pmap M.! port 
                                    pkey = last $ roleKeys ?role in
                                let -- P4 ingress port numbers are 32-bit
                                    ?kmap = M.insert (name pkey) (EBinOp nopos Minus ingressPort (EInt nopos 32 $ fromIntegral first)) kmap in 
                                mkStatement (roleBody ?role))
             $ nodePorts switch
    let groups = zip stats portranges
    -- If there are multiple port groups, generate a top-level switch
    return $ foldl' (\st (st', (first, last)) -> let bound1 = EBinOp nopos Gte ingressPort (EInt nopos 32 $ fromIntegral first)
                                                     bound2 = EBinOp nopos Lte ingressPort (EInt nopos 32 $ fromIntegral last)
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
        portnum = evalExpr $ EBinOp nopos Plus (EInt nopos 32 $ fromIntegral base) (last ks) 
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
 

