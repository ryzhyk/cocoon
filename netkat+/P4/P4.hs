{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

-- Convert NetKAT+ spec to P4

module P4.P4( P4DynAction(..)
            , genP4Switches
            , genP4Switch
            , populateTable) where

import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Bits
import qualified Data.Map as M
import Numeric

import Util
import PP
import Syntax
import Pos
import NS
import Name
import Eval
import Topology
import Type
import P4.Header

{-

Compilation consists of two phases: the compile-time phase produces control blocks,
tables and actions.  The runtime phase is only allowed to modify tables.  Specifically,
these modifications happen when a function that was undefined at compile time is given
a definition by the user.  Given P4 restrictions, not any function definition can be
encoded via table entries.  For example, the following definition

func(pkt) = case { pkt.f1 = const: pkt.f2 }

requires passing field f2 of the packet to an action defined at compile time.  This is 
impossible, since P4 match tables do not allow actions with non-const parameters.

-} 


-- Dynamic action, i.e., action that depends on expression that can change at run time
-- and must be encoded in a P4 table maintained by the controller at runtime
data P4DynAction = P4DynAction { p4dynTable  :: String       -- name of the table
                               , p4dynExpr   :: Expr         -- expression that the table computes
                               , p4dynAction :: Maybe String -- name of action to invoke. If false, it's a yes-no action
                               }

-- State maintained during compilation
data P4State = P4State { p4TableCnt   :: Int   -- table counter
                       , p4Tables     :: [Doc] -- table specifications
                       , p4Commands   :: [Doc] -- commands to go to the command file
                       , p4DynActions :: [P4DynAction]
                       }

data P4Statement = P4SSeq   P4Statement P4Statement
                 | P4SITE   Expr P4Statement (Maybe P4Statement)
                 | P4SApply String (Maybe [(String, P4Statement)])
                 | P4SDrop

isITE :: P4Statement -> Bool
isITE (P4SITE _ _ _) = True
isITE _              = False

-- Port map: stores physical port range for each input and output port of the switch
type PMap = M.Map String (Int,Int)

egressSpec, ingressPort :: Expr
egressSpec  = EField nopos (EVar nopos "standard_metadata") "egress_spec"
ingressPort = EField nopos (EVar nopos "standard_metadata") "ingress_port"

instance PP P4Statement where
    pp (P4SSeq s1 s2)         = pp s1 $$ pp s2
    pp (P4SITE c t e)         = (pp "if" <+> (parens $ printExpr c) <+> lbrace)
                                $$
                                (nest' $ pp t)
                                $$
                                maybe rbrace (\st -> (rbrace <+> pp "else" <+> (if' (isITE st) empty lbrace)) 
                                                     $$ (nest' $ pp st)
                                                     $$ (if' (isITE st) empty rbrace)) e
    pp (P4SApply n Nothing)   = pp "apply" <> (parens $ pp n) <> semi
    pp (P4SApply n (Just as)) = (pp "apply" <> (parens $ pp n) <> lbrace)
                                $$
                                (nest' $ vcat $ map (\(a, s) -> (pp a <+> lbrace) $$ (nest' $ pp s) $$ rbrace) as)
                                $$ 
                                (rbrace <> semi)
    pp (P4SDrop)              = pp "drop" <> semi

-- We don't use a separate type for P4 expressions for now, 
-- just represent them as Expr
printExpr :: Expr -> Doc
printExpr (EVar _ k)        = pp k
printExpr (EPacket _)       = pp "pkt"
printExpr (EField _ e f)    = printExpr e <> char '.' <> pp f
printExpr (EBool _ True)    = pp "true"
printExpr (EBool _ False)   = pp "false"
printExpr (EInt _ _ v)      = pp $ show v
printExpr (EBinOp _ op l r) = parens $ (printExpr l) <+> printBOp op <+> (printExpr r)
printExpr (EUnOp _ op e)    = parens $ printUOp op <+> printExpr e
printExpr e                 = error $ "P4.printExpr " ++ show e

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

-- True if expression cannot be interpreted at compile time and requires a P4 table.
exprNeedsTable :: Expr -> Bool
exprNeedsTable (EVar _ _)         = False
exprNeedsTable (EPacket _)        = False
exprNeedsTable (EApply _ _ _)     = True
exprNeedsTable (EField _ s _)     = exprNeedsTable s
exprNeedsTable (ELocation _ _ as) = or $ map exprNeedsTable as
exprNeedsTable (EBool _ _)        = False
exprNeedsTable (EInt _ _ _)       = False
exprNeedsTable (EStruct _ _ fs)   = or $ map exprNeedsTable fs
exprNeedsTable (EBinOp _ _ e1 e2) = exprNeedsTable e1 || exprNeedsTable e2
exprNeedsTable (EUnOp _ _ e)      = exprNeedsTable e
exprNeedsTable (ECond _ cs d)     = (or $ map (\(c,e) -> exprNeedsTable c || exprNeedsTable e) cs) || exprNeedsTable d


incTableCnt :: State P4State Int
incTableCnt = do
    n <- gets p4TableCnt
    modify (\s -> s{p4TableCnt = n + 1})
    return n

-- Generate all P4 switches in the topology
genP4Switches :: Refine -> Topology -> [(InstanceDescr, (Doc, Doc, [P4DynAction]))]
genP4Switches r topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = M.fromList $ concatMap (\((i,o),range,_) -> [(i,range),(o,range)]) links
                                                          in (descr, genP4Switch r switch kmap pmap)) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology

--  Generate P4 switch. Returns to strings: one containing the P4 description
--  of the switch, and one containing runtime commands to initialize switch tables.
genP4Switch :: Refine -> Node -> KMap -> PMap -> (Doc, Doc, [P4DynAction])
genP4Switch r switch kmap pmap = 
    let ?r = r in
    let ?pmap = pmap in
    let (controlstat, P4State _ tables commands dynacts) = runState (mkSwitch kmap switch) (P4State 0 [] [] []) 
        control = (pp "control" <+> pp "ingress" <+> lbrace)
                  $$
                  (nest' $ pp controlstat)
                  $$
                  rbrace
    in (pp p4HeaderDecls $$ pp "" $$ vcat tables $$ pp "" $$ control, vcat commands, dynacts)

mkSwitch :: (?r::Refine, ?pmap::PMap) => KMap -> Node -> State P4State P4Statement
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
    return $ foldl' (\st (st', (first, lst)) -> let bound1 = EBinOp nopos Gte ingressPort (EInt nopos 32 $ fromIntegral first)
                                                    bound2 = EBinOp nopos Lte ingressPort (EInt nopos 32 $ fromIntegral lst)
                                                    cond = EBinOp nopos And bound1 bound2
                                                 in P4SITE cond st' (Just st)) 
                    (fst $ head groups) (tail groups)

mkStatement :: (?r::Refine, ?role::Role, ?kmap::KMap, ?pmap::PMap) => Statement -> State P4State P4Statement
mkStatement (SSeq  _ s1 s2) = do 
    s1' <- mkStatement s1
    s2' <- mkStatement s2
    return $ P4SSeq s1' s2'

mkStatement (SPar  _ _ _)   = error "Not implemented: P4.mkStatement: SPar"

mkStatement (SITE  _ c t e) = do
    let c' = liftConds $ evalExpr c
    case c' of
         EBool _ True  -> mkStatement t
         EBool _ False -> maybe (return P4SDrop) mkStatement e
         _             -> do t' <- mkStatement t
                             e' <- maybe (return Nothing) (liftM Just . mkStatement) e 
                             if exprNeedsTable c'
                                then do tableid <- incTableCnt
                                        let tablename = "cond" ++ show tableid
                                        mkCondTable tablename c'
                                        return $ P4SApply tablename $ Just $ ("yes", t'):(maybe [] (return . ("no",)) e')
                                else return $ P4SITE c' t' e'

mkStatement (STest _ e)     = do
    let e' = liftConds $ evalExpr e
    case e' of
         EBool _ False -> return P4SDrop
         _             -> if exprNeedsTable e'
                             then do tableid <- incTableCnt
                                     let tablename = "test" ++ show tableid
                                     mkCondTable tablename e'
                                     return $ P4SApply tablename $ Just [("miss", P4SDrop)]
                             else return $ P4SITE (EUnOp nopos Not e') P4SDrop Nothing

-- Make sure that assignment statements do not contain case-expressions in the RHS.
mkStatement (SSet  _ lhs rhs) = do
    let lhs' = evalExpr lhs
        rhs' = liftConds $ evalExpr rhs
    let assignToCascade l (ECond _ [] d)         = assignToCascade l d
        assignToCascade l (ECond _ ((c,v):cs) d) = SITE nopos c (assignToCascade l v) (Just $ assignToCascade l (ECond nopos cs d))
        assignToCascade l v                      = SSet nopos l v
    case rhs' of 
         ECond _ _ _ -> mkStatement $ assignToCascade lhs' rhs'
         _           -> do tableid <- incTableCnt
                           let tablename = "set" ++ show tableid
                           mkAssignTable tablename lhs' rhs'
                           return $ P4SApply tablename Nothing

mkStatement (SSend _ dst) = do
    let dst' = liftConds $ evalExpr dst
    let sendToCascade (ECond _ [] d)         = sendToCascade d
        sendToCascade (ECond _ ((c,v):cs) d) = SITE nopos c (sendToCascade v) (Just $ sendToCascade (ECond nopos cs d))
        sendToCascade v                      = SSend nopos v
    case dst' of
         ECond _ _ _ -> mkStatement $ sendToCascade dst'
         _           -> do let ELocation _ n ks = dst'
                           let (base, _) = ?pmap M.! n
                               portnum = evalExpr $ EBinOp nopos Plus (EInt nopos 32 $ fromIntegral base) (last ks) 
                           tableid <- incTableCnt
                           let tablename = "send" ++ show tableid
                           mkAssignTable tablename egressSpec portnum
                           return $ P4SApply tablename Nothing

-- convert expression into a cascade of ECond's, such
-- that their leaf expressions do not contain any EConds
liftConds :: (?r::Refine, ?role::Role, ?kmap::KMap) => Expr -> Expr
liftConds = evalExpr . liftConds'

liftConds' :: (?r::Refine, ?role::Role, ?kmap::KMap) => Expr -> Expr
liftConds' e = 
    case e of 
         EVar _ _          -> e
         EPacket _         -> e
         EApply _ f as     -> combineCascades (EApply nopos f) $ map liftConds' as
         EField _ s f      -> combineCascades (\[s'] -> EField nopos s' f) [liftConds' s]
         ELocation _ r as  -> combineCascades (ELocation nopos r) $ map liftConds' as
         EBool _ _         -> e
         EInt _ _ _        -> e
         EStruct _ s fs    -> combineCascades (EStruct nopos s) $ map liftConds' fs
         EBinOp _ op e1 e2 -> combineCascades (\[e1', e2'] -> EBinOp nopos op e1' e2') [liftConds' e1, liftConds' e2]
         EUnOp _ op v      -> combineCascades (EUnOp nopos op . head) [liftConds' v]
         ECond _ cs d      -> let d' =liftConds' d in
                              case d' of  
                                   ECond _ dcs dd -> ECond nopos ((map (\(c,v) -> (liftConds' c, liftConds' v)) cs)++dcs) dd
                                   _              -> ECond nopos (map (\(c,v) -> (liftConds' c, liftConds' v)) cs)        d'
    where combineCascades f es  = combineCascades' f es [] 
          combineCascades' f ((ECond _ cs d):es) es' = ECond nopos (map (mapSnd (\v -> combineCascades' f (v:es) es')) cs) (combineCascades' f (d:es) es')
          combineCascades' f (v:es) es'              = combineCascades' f es (es' ++ [v])
          combineCascades' f [] es'                  = f es'

mkAssignTable :: (?r::Refine, ?role::Role) => String -> Expr -> Expr -> State P4State ()
mkAssignTable n lhs rhs = do
    let actname = "a_" ++ n
        isdyn = exprNeedsTable rhs
        action = if isdyn
                    then (pp "action" <+> pp actname <> parens (pp "_val") <+> lbrace)
                         $$
                         (nest' $ pp "modify_field" <> (parens $ printExpr lhs <> comma <+> pp "_val") <> semi)
                         $$
                         rbrace
                    else (pp "action" <+> pp actname <> parens empty <+> lbrace)
                         $$
                         (nest' $ pp "modify_field" <> (parens $ printExpr lhs <> comma <+> printExpr rhs) <> semi)
                         $$
                         rbrace
        dyn = if isdyn
                 then [P4DynAction n rhs $ Just actname]
                 else []
        table = action
                $$
                (pp "table" <+> pp n <+> lbrace)
                $$
                (if isdyn 
                    then (nest' $ pp "reads" <+> (braces $ hsep $ map (\f -> printExpr f <> pp ": ternary" <> semi) pktFields)) 
                    else empty)
                $$
                (nest' $ pp "actions" <+> (braces $ pp actname <> semi))
                $$
                rbrace
        command = if isdyn 
                     then []
                     else [pp "table_set_default" <+> pp n <+> pp actname]
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [table]
                     , p4Commands = p4Commands p4 ++ command
                     , p4DynActions = p4DynActions p4 ++ dyn})
 
mkCondTable :: (?r::Refine, ?role::Role) => String -> Expr -> State P4State ()
mkCondTable n e = do
    let table = (pp "table" <+> pp n <+> lbrace)
                $$
                (nest' $ pp "reads" <+> (braces $ hsep $ map (\f -> printExpr f <> pp ": ternary" <> semi) pktFields))
                $$
                (nest' $ pp "actions" <+> (braces $ pp "yes" <> semi <+> pp "no" <> semi))
                $$
                rbrace
        command = pp "table_set_default" <+> pp n <+> pp "no"
        dyn = P4DynAction n e Nothing
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [table]
                     , p4Commands = p4Commands p4 ++ [command]
                     , p4DynActions = p4DynActions p4 ++ [dyn]})

pktFields :: (?r::Refine, ?role::Role) => [Expr]
pktFields = fields (EPacket nopos)
    where fields e = case typ' ?r (CtxRole ?role) e of
                          TStruct _ fs -> concatMap (\f -> fields (EField nopos e $ name f)) fs
                          _            -> [e]

-----------------------------------------------------------------
-- Generate runtime updates to P4 tables
-----------------------------------------------------------------

populateTable :: (?r::Refine, ?role::Role, ?kmap::KMap) => P4DynAction -> [Doc]
populateTable P4DynAction{..} = 
    case p4dynAction of
         Nothing -> mapIdx (\(msk,val) i -> case val of
                                                 EBool _ True  -> mkTableEntry p4dynTable "yes" [] msk (nentries - i)
                                                 EBool _ False -> mkTableEntry p4dynTable "no"  [] msk (nentries - i)
                                                 _             -> error $ "Non-constant boolean value " ++ show val ++ "") es
         Just a  -> mapIdx (\(msk,val) i -> mkTableEntry p4dynTable a [exprToVal val] msk (nentries - i)) es
    where es = concatMap (\(c,v) -> map (,v) $ exprToMasks c) 
               $ flattenConds 
               $ liftConds 
               $ evalExpr p4dynExpr
          nentries = length es

-- Flatten cascading cases into a sequence of (condition, value) pairs
-- in the order of decreasing priority.
flattenConds :: Expr -> [(Expr, Expr)]
flattenConds = flattenConds' []

flattenConds' :: [Expr] -> Expr -> [(Expr, Expr)]
flattenConds' es (ECond _ cs d) = (concatMap (\(c,e) -> flattenConds' (es ++ [c]) e) cs) ++ (flattenConds' es d)
flattenConds' es e              = [(conj es, e)]

--mkDefaultEntry :: String -> String -> [Doc] -> Doc
--mkDefaultEntry table action args = 
--    pp "table_set_default" <+> pp table <+> pp action <+> (hsep args)

mkTableEntry :: String -> String -> [Doc] -> Doc -> Int -> Doc
mkTableEntry table action args mask priority = 
    pp "table_add" <+> pp table <+> pp action <+> mask <+> pp "=>" <+> (hsep args) <+> pp priority

-- Compile boolean expression into one or more P4 match entries,
-- in the order of decreasing priority.
-- e may not contain variables (other than pkt), function calls,
-- case{} expressions.
exprToMasks :: (?r::Refine, ?role::Role) => Expr -> [Doc]
exprToMasks e = map disjunctToMask $ exprToDNF e

exprToDNF :: (?r::Refine, ?role::Role) => Expr -> [[Expr]]
exprToDNF (EBinOp _ And e1 e2) = concatMap (\d -> map (d++) $ exprToDNF e2) (exprToDNF e1)
exprToDNF (EBinOp _ Or e1 e2)  = exprToDNF e1 ++ exprToDNF e2
exprToDNF e@(EBinOp _ Eq e1 e2)  = 
    case typ' ?r (CtxRole ?role) e1 of
         TStruct _ fs -> exprToDNF $ conj $ map (\f -> EBinOp nopos Eq (EField nopos e1 $ name f) (EField nopos e2 $ name f)) fs
         TUInt _ _    -> [[e]]
         _            -> error $ "Cannot convert expression " ++ show e ++ " to DNF" 
exprToDNF e = error $ "Cannot convert expression " ++ show e ++ " to DNF" 

disjunctToMask :: (?r::Refine, ?role::Role) => [Expr] -> Doc
disjunctToMask atoms = mkMatch $ map atomToMatch atoms

-- maps atom of the form (x = const) to a (field_name, value)  
atomToMatch :: Expr -> (Expr, String)
atomToMatch e =
    case e of
         EBinOp _ Eq e1 (EInt _ _ i) -> (e1, "0x" ++ showHex i "")
         EBinOp _ Eq (EInt _ _ i) e2 -> (e2, "0x" ++ showHex i "")
         _                           -> error $ "Not implemented: P4.aromToMatch " ++ show e

-- Convert a list of (field,value) pairs into a P4 table match clause
-- by ordering the fields in the order required by the table and adding
-- don't care masks for all other fields.
mkMatch :: (?r::Refine, ?role::Role) => [(Expr,String)] -> Doc
mkMatch atoms = hsep $ map (\e -> let TUInt _ w = typ' ?r (CtxRole ?role) e in
                                  case lookup e atoms of
                                       Nothing -> pp "0x0" <> pp "&&&" <> pp "0x0"
                                       Just v  -> pp v  <> pp "&&&" <> pp "0x" <> pp (showHex (mask w) "")) pktFields
    where mask w = foldl' (\a i -> setBit a i) (0::Integer) [0..w-1]

exprToVal :: Expr -> Doc
exprToVal (EInt _ _ i) = pp $ "0x" ++ showHex i ""
exprToVal e            = error $ "P4.exprToVal " ++ show e
