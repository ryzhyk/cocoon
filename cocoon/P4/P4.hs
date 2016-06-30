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
{-# LANGUAGE ImplicitParams, TupleSections, RecordWildCards #-}

-- Convert Cocoon spec to P4

module P4.P4( P4DynAction(..)
            , P4Switch(..)
            , genP4Switches
            , populateTable) where

import Control.Monad.State
import Text.PrettyPrint
import Data.List
import Data.Bits
import qualified Data.Map as M
import Numeric
import qualified Data.Set as S
import Debug.Trace

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
import Expr
import Builtins

{-

Compilation consists of two phases: the compile-time phase produces control blocks,
tables and actions.  The runtime phase is only allowed to modify tables.  Specifically,
these modifications happen when a function that was undefined at compile time is given
a definition by the user.  Given P4 restrictions, not any function definition can be
encoded via table entries.  For example, the following definition

func(pkt) = case { pkt.f1 = const: pkt.f2 }
                 import Debug.Trace

requires passing field f2 of the packet to an action defined at compile time.  This is 
impossible, since P4 match tables do not allow actions with non-const parameters.

-} 

-- Maximal size of a tabular representation of expression
maxExprTable :: Integer
maxExprTable = 1000

tmpVarName :: String -> String
tmpVarName sname = "_tmp_" ++ sname

localVarName :: Role -> String -> String
localVarName rl vname = "_" ++ name rl ++ "_" ++ vname

-- Dynamic action, i.e., action that depends on expression that can change at run time
-- and must be encoded in a P4 table maintained by the controller at runtime
data P4DynAction = P4DynAction { p4dynTable  :: String       -- name of the table
                               , p4dynRole   :: Role         -- role that the action belongs to
                               , p4dynKMap   :: KMap
                               , p4dynExpr   :: Expr         -- expression that the table computes
                               , p4dynAction :: Maybe String -- name of action to invoke. If Nothing, it's a yes-no action
                               }

-- State maintained during compilation
data P4State = P4State { p4Structs    :: S.Set String -- struct types that occur in local variable declarations
                       , p4Vars       :: [Doc]        -- local variables
                       , p4TableCnt   :: Int          -- table counter
                       , p4Tables     :: [Doc]        -- table specifications
                       , p4Commands   :: [Doc]        -- commands to go to the command file
                       , p4DynActions :: [P4DynAction]
                       }

data P4Statement = P4SSeq   P4Statement P4Statement
                 | P4SITE   Doc P4Statement (Maybe P4Statement)
                 | P4SApply String (Maybe [(String, P4Statement)])
                 | P4SDrop
                 | P4SNop

isITE :: P4Statement -> Bool
isITE (P4SITE _ _ _) = True
isITE _              = False

-- Port map: stores physical port range for each input and output port of the switch
type PMap = M.Map String (Int,Int)

egressSpec, ingressPort :: Expr
egressSpec  = EField nopos (EField nopos (EPacket nopos) "standard_metadata") "egress_spec"
ingressPort = EField nopos (EField nopos (EPacket nopos) "standard_metadata") "ingress_port"

instance PP P4Statement where
    pp (P4SSeq s1 s2)         = pp s1 $$ pp s2
    pp (P4SITE c t e)         = (pp "if" <+> (parens c) <+> lbrace)
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
                                rbrace
    pp (P4SDrop)              = pp "drop" <> semi
    pp (P4SNop)               = pp "{}"

p4seq :: [P4Statement] -> P4Statement
p4seq []      = P4SNop
p4seq [s]     = s
p4seq (s1:ss) = P4SSeq s1 $ p4seq ss

-- We don't use a separate type for P4 expressions for now, 
-- just represent them as Expr
printExpr :: (?r::Refine, ?role::Role, ?pmap::PMap) => Expr -> Doc
printExpr (EVar _ k)                            = if k == name pkey 
                                                     then printExpr $ EBinOp nopos Minus ingressPort (EInt nopos 32 $ fromIntegral first)
                                                     else case lookupLocalVar ?role k of
                                                               Nothing -> pp k
                                                               Just _  -> pp $ localVarName ?role k
    where pkey = last $ roleKeys ?role
          (first, _) = ?pmap M.! (name ?role)
printExpr (EPacket _)                           = pp "pkt"
printExpr (EField _ e f) | f == "valid"         = pp "valid" <> (parens $ printExpr e)
printExpr (EField _ (EPacket _) f)              = pp f
printExpr (EField _ e@(EVar _ _) f)             = printExpr e <> char '.' <> pp f
printExpr (EField _ (EField _ (EPacket _) h) f) = pp h <> char '.' <> pp f
printExpr (EField _ e f)                        = printExpr e <> char '_' <> pp f
printExpr (EBool _ True)                        = pp "true"
printExpr (EBool _ False)                       = pp "false"
printExpr (EInt _ _ v)                          = pp $ show v
printExpr (EBinOp _ Impl l r)                   = printExpr $ EBinOp nopos Or (EUnOp nopos Not l) r
printExpr (EBinOp _ Concat l r)                 = parens $ (parens $ (cast w (printExpr l)) <+> pp "<<" <+> pp w2) <+> pp "|" <+> (cast w $ printExpr r)
    where TUInt _ w1 = typ' ?r (CtxRole ?role) l
          TUInt _ w2 = typ' ?r (CtxRole ?role) r
          w = w1 + w2
printExpr (EBinOp _ Eq l r)                     = 
    let ?c = CtxRole ?role in
    let lscalars = map (evalExpr M.empty) $ exprScalars ?r (CtxRole ?role) l
        rscalars = map (evalExpr M.empty) $ exprScalars ?r (CtxRole ?role) r in 
    parens $ hsep $ punctuate (pp "and") 
                  $ map (\(l', r') -> case let ?kmap = M.empty in liftConds True (EBinOp nopos Eq l' r') of
                                           EBinOp _ Eq l'' r'' -> parens $ (printExpr l'') <+> pp "==" <+> (printExpr r'')
                                           e                   -> printExpr e) 
                  $ zip lscalars rscalars
printExpr (EBinOp _ op l r)                     = parens $ (printExpr l) <+> printBOp op <+> (printExpr r)
printExpr (EUnOp _ op e)                        = parens $ printUOp op <+> printExpr e
printExpr (ESlice _ e h l)                      = cast (h-l+1) $ parens $ (parens $ printExpr e <+> pp ">>" <+> pp l) <+> pp "&" <+> 
                                                                          (pp $ "0x" ++ showHex (2^(h-l+1) - 1::Integer) "")
printExpr (EApply _ f as)                       = (bfuncPrintP4 $ getBuiltin f) ?r (CtxRole ?role) as $ map printExpr as
printExpr e                                     = error $ "P4.printExpr " ++ show e

cast :: Int -> Doc -> Doc
cast w e = parens $ (parens $ pp "bit<" <> pp w <> pp ">") <> e

printBOp :: BOp -> Doc
printBOp Eq     = pp "=="
printBOp Neq    = pp "!="
printBOp Lt     = pp "<"
printBOp Gt     = pp ">"
printBOp Lte    = pp "<="
printBOp Gte    = pp ">="
printBOp And    = pp "and"
printBOp Or     = pp "or"
printBOp Plus   = pp "+"
printBOp Minus  = pp "-"
printBOp Mod    = pp "%"
printBOp ShiftR = pp ">>"
printBOp ShiftL = pp "<<"
printBOp Concat = error "P4.printBOp ++"
printBOp Impl   = error "P4.printBOp =>"

printUOp :: UOp -> Doc
printUOp Not   = pp "not"

-- True if expression cannot be interpreted at compile time and requires a P4 table.
exprNeedsTable :: Expr -> Bool
exprNeedsTable e = exprNeedsTable' e

exprNeedsTable' :: Expr -> Bool
exprNeedsTable' (EVar _ _)         = False
exprNeedsTable' (EDotVar _ _)      = False
exprNeedsTable' (EPacket _)        = False
exprNeedsTable' (EApply _ _ _)     = True
exprNeedsTable' (EBuiltin _ _ as)  = or $ map exprNeedsTable' as
exprNeedsTable' (EField _ s _)     = exprNeedsTable' s
exprNeedsTable' (ELocation _ _ as) = or $ map exprNeedsTable' as
exprNeedsTable' (EBool _ _)        = False
exprNeedsTable' (EInt _ _ _)       = False
exprNeedsTable' (EStruct _ _ fs)   = or $ map exprNeedsTable' fs
exprNeedsTable' (EBinOp _ _ e1 e2) = exprNeedsTable' e1 || exprNeedsTable' e2
exprNeedsTable' (EUnOp _ _ e)      = exprNeedsTable' e
exprNeedsTable' (ESlice _ e _ _)   = exprNeedsTable' e
exprNeedsTable' (ECond _ cs d)     = (or $ map (\(c,e) -> exprNeedsTable' c || exprNeedsTable' e) cs) || exprNeedsTable' d


incTableCnt :: State P4State Int
incTableCnt = do
    n <- gets p4TableCnt
    modify (\s -> s{p4TableCnt = n + 1})
    return n

data P4Switch = P4Switch { p4Descr   :: InstanceDescr
                         , p4Prog    :: Doc             -- P4 description of the switch
                         , p4Init    :: Doc             -- switch initialization commands
                         , p4DynActs :: [P4DynAction]   -- dynamic actions to be programmed at runtime
                         }

-- Generate all P4 switches in the topology
genP4Switches :: Refine -> Topology -> [P4Switch]
genP4Switches r topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = M.fromList $ concatMap (\((i,o),range,_) -> [(i,range),(o,range)]) links
                                                              (prog, initial, acts) = genP4Switch r switch kmap pmap
                                                          in P4Switch descr prog initial acts) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology

-- Generate P4 switch. Returns two strings: one containing the P4 description
-- of the switch, and one containing runtime commands to initialize switch tables.
genP4Switch :: Refine -> Node -> KMap -> PMap -> (Doc, Doc, [P4DynAction])
genP4Switch r switch kmap pmap = 
    let ?r = r in
    let ?pmap = pmap in
    let (controlstat, P4State structs lvars _ tables commands dynacts) = runState (mkSwitch kmap switch) (P4State S.empty [] 0 [] [pp p4DefaultDecls] []) 
        control = (pp "control" <+> pp "ingress" <+> lbrace)
                  $$
                  (nest' $ pp controlstat)
                  $$
                  rbrace
    in ( pp p4HeaderDecls $$ pp "" $$ vcat (map mkStructType $ S.toList structs) $$ vcat lvars $$ vcat tables $$ pp "" $$ control
       , vcat commands
       , dynacts)

mkStructType :: (?r::Refine) => String -> Doc
mkStructType n = (pp "header_type" <+> pp n <+> lbrace)
                 $$
                 (nest' $ pp "fields" <> lbrace
                          $$
                          (nest' $ vcat $ map (\f -> case typ' ?r undefined f of
                                                          TBool _   -> pp "bool"
                                                          TUInt _ w -> pp "bit<" <> pp w <> pp ">"
                                                          _         -> error "P4.mkStructType: only bool and uint fields are supported"
                                                     <+> (pp $ name f) <> semi) fs) 
                          $$
                          rbrace)
                 $$
                 rbrace
    where TStruct _ fs = tdefType $ getType ?r n


mkSwitch :: (?r::Refine, ?pmap::PMap) => KMap -> Node -> State P4State P4Statement
mkSwitch kmap switch = do
    -- get the list of port numbers for each port group
    let portranges = map (\(port,_) -> ?pmap M.! port) $ nodePorts switch
    stats <- mapM (\(port,_) -> do let ?role = getRole ?r port
                                   let ?c = CtxRole ?role
                                   let ?kmap = kmap 
                                   mkStatement (roleBody ?role))
             $ nodePorts switch
    let groups = zip stats portranges
    -- If there are multiple port groups, generate a top-level switch
    return $ foldl' (\st (st', (first, lst)) -> let cond = parens $ pp "standard_metadata.ingress_port >=" <+> pp first <+> pp "and" <+> 
                                                                    pp "standard_metadata.ingress_port <=" <+> pp lst
                                                in P4SITE cond st' (Just st)) 
                    (fst $ head groups) (tail groups)

mkStatement :: (?r::Refine, ?role::Role, ?c::ECtx, ?kmap::KMap, ?pmap::PMap) => Statement -> State P4State P4Statement
mkStatement (SSeq  _ s1 s2) = do 
    s1' <- mkStatement s1
    s2' <- mkStatement s2
    return $ P4SSeq s1' s2'

mkStatement (SPar  _ _ _)   = error "Not implemented: P4.mkStatement: SPar"

mkStatement (SITE  _ c t e) = do
    let c' = liftConds True $ evalExpr' c
    if exprNeedsTable c'
       then do t' <- mkStatement t
               e' <- maybe (return Nothing) (liftM Just . mkStatement) e
               tableid <- incTableCnt
               let tablename = "cond" ++ show tableid
               mkCondTable tablename c'
               return $ P4SApply tablename $ Just $ ("yes", t'):(maybe [] (return . ("no",)) e')
       else iteFromCascade (Right t) (fmap Right e) c'

mkStatement (STest _ e)     = do
    let e' = liftConds True $ evalExpr' $ EUnOp nopos Not e
    if exprNeedsTable e'
       then do tableid <- incTableCnt
               let tablename = "test" ++ show tableid
               mkCondTable tablename e'
               return $ P4SApply tablename $ Just [("hit", P4SDrop)]
       else iteFromCascade (Left P4SDrop) Nothing e'

-- Make sure that assignment statements do not contain case-expressions in the RHS.
mkStatement (SSet  _ lhs rhs) | exprIsValidFlag lhs = do
    let lhs' = evalExpr' lhs
        rhs' = evalExpr' rhs
    setValid lhs' rhs'

mkStatement (SSet  _ lhs rhs) = do
    let lhs' = evalExpr' lhs
        rhs' = liftConds True $ evalExpr' rhs
    let local = case lhs of 
                     EVar _ _ -> True
                     _        -> False
    let setValidCascade l (ECond _ [] d)         = setValidCascade l d
        setValidCascade l (ECond _ ((c,v):cs) d) = SITE nopos c (setValidCascade l v) (Just $ setValidCascade l (ECond nopos cs d))
        setValidCascade l v                      = SSet nopos l v
    let assignToCascade l (ECond _ [] d)         = assignToCascade l d
        assignToCascade l (ECond _ ((c,v):cs) d) = SITE nopos c (assignToCascade l v) (Just $ assignToCascade l (ECond nopos cs d))
        assignToCascade l v                      = SSet nopos l v
    let table l r = do tableid <- incTableCnt
                       let tablename = "set" ++ show tableid
                       mkAssignTable tablename l r
                       return $ P4SApply tablename Nothing
    case rhs' of 
         ECond _ _ _ -> mkStatement $ assignToCascade lhs' rhs'
         _           -> if isStruct ?r ?c rhs'
                           then do let TUser _ sname = typ'' ?r ?c lhs'
                                       lscalars = map evalExpr' $ exprScalars ?r ?c lhs
                                       rscalars = map (liftConds True . evalExpr') $ exprScalars ?r ?c rhs
                                       tscalars = map (exprSubst lhs (EVar nopos $ tmpVarName sname)) lscalars
                                       atoms = filter (\(l,_,_) -> not $ exprIsValidFlag l) $ zip3 lscalars rscalars tscalars
                                   if local 
                                      then do copy <- mapM (\(l,r,_) -> mkStatement (SSet nopos l r)) atoms
                                              return $ p4seq copy
                                      else do -- For all fields that are not valid flags
                                              --     copy field to tmp
                                              copy1 <- mapM (\(_,r,t) -> mkStatement (SSet nopos t r)) atoms
                                              -- Does it have a valid flag? 
                                              --     Yes: apply add_/rm_ first
                                              copyv <- case find (exprIsValidFlag . fst) $ zip lscalars rscalars of
                                                            Nothing     -> return []
                                                            Just (l, r) -> do s <- mkStatement $ setValidCascade l r
                                                                              return [s]
                                              -- For all fields that are not valid flags
                                              --     copy tmp to lhs
                                              copy2 <- mapM (\(l,_,t) -> table l t) atoms
                                              return $ p4seq $ copy1 ++ copyv ++ copy2
                           else table lhs' rhs'


mkStatement (SSend _ dst) = do
    let dst' = liftConds True $ evalExpr' dst
    let sendToCascade (ECond _ [] d)         = sendToCascade d
        sendToCascade (ECond _ ((c,v):cs) d) = SITE nopos c (sendToCascade v) (Just $ sendToCascade (ECond nopos cs d))
        sendToCascade v                      = SSend nopos v
    case dst' of
         ECond _ _ _ -> mkStatement $ sendToCascade dst'
         _           -> do let ELocation _ n ks = dst'
                           let (base, _) = ?pmap M.! n
                               portnum = evalExpr' $ EBinOp nopos Plus (EInt nopos 32 $ fromIntegral base) (last ks) 
                           tableid <- incTableCnt
                           let tablename = "send" ++ show tableid
                           mkAssignTable tablename egressSpec portnum
                           return $ P4SApply tablename Nothing

mkStatement (SSendND _ _ _) = error "P4.mkStatement SSendND"
mkStatement (SHavoc _ _)    = error "P4.mkStatement SHavoc"
mkStatement (SAssume _ _)   = error "P4.mkStatement SAssume"
mkStatement (SLet _ t v e)  = do 
    modify (\s -> s{p4Vars = (p4Vars s) ++ [mkLocalVar t v]})
    case typ'' ?r ?c t of
         TUser _ n -> modify (\s -> s{p4Structs = S.insert n (p4Structs s)})
         _         -> return ()
    mkStatement $ SSet nopos (EVar nopos v) e
mkStatement (SFork _ _ _ _) = error "Not implemented: P4.mkStatement SFork"

mkLocalVar :: (?r::Refine, ?c::ECtx, ?role::Role) => Type -> String -> Doc
mkLocalVar t n = pp "metadata" <+> tname <+> (pp $ localVarName ?role n) <> semi
    where tname = case typ'' ?r ?c t of
                       TUInt _ w -> pp "bit<" <> pp w <> pp ">"
                       TBool _   -> pp "bool"
                       TUser _ s -> pp s
                       _         -> error "P4.mkLocalVar: unexpected type"

mkAddHeader :: String -> State P4State P4Statement
mkAddHeader h = do
    tableid <- incTableCnt
    let tablename = "add" ++ show tableid
        actname = "a_" ++ tablename
        action = pp "action" <+> pp actname <> pp "()" <+> lbrace
                 $$
                 (nest' $ pp "add_header" <> (parens $ pp h) <> semi)
                 $$
                 (nest' $ pp $ p4InitHeader h)
                 $$
                 rbrace
        table = (pp "table" <+> pp tablename <+> lbrace)
                $$
                (nest' $ pp "actions" <+> (braces $ pp actname <> semi))
                $$
                rbrace
        command = pp "table_set_default" <+> pp tablename <+> pp actname
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [action $$ table]
                     , p4Commands = p4Commands p4 ++ [command]})
    return $ P4SApply tablename Nothing

mkRmHeader :: String -> State P4State P4Statement
mkRmHeader h = do
    tableid <- incTableCnt
    let tablename = "rm" ++ show tableid
        actname = "a_" ++ tablename
        action = pp "action" <+> pp actname <> pp "()" <+> lbrace
                 $$
                 (nest' $ pp $ p4CleanupHeader h)
                 $$
                 (nest' $ pp "remove_header" <> (parens $ pp h) <> semi)
                 $$
                 rbrace
        table = pp "table" <+> pp tablename <+> lbrace
                $$
                (nest' $ pp "actions" <+> (braces $ pp actname <> semi))
                $$
                rbrace
        command = pp "table_set_default" <+> pp tablename <+> pp actname
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [action $$ table]
                     , p4Commands = p4Commands p4 ++ [command]})
    return $ P4SApply tablename Nothing


setValid :: (?r::Refine, ?role::Role, ?pmap::PMap) => Expr -> Expr -> State P4State P4Statement
setValid l r = do
    let EField _ h _ = l 
    let hname = render $ printExpr h
    case r of
         EBool _ True  -> do add <- mkAddHeader hname
                             return $ P4SITE (printExpr $ EUnOp nopos Not l) add Nothing
         EBool _ False -> do rm <- mkRmHeader (render $ printExpr h)
                             return $ P4SITE (printExpr l) rm Nothing
         _             -> error $ "P4.setValid " ++ show l ++ " " ++ show r


iteFromCascade :: (?r::Refine, ?role::Role, ?c::ECtx, ?kmap::KMap, ?pmap::PMap) => Either P4Statement Statement -> Maybe (Either P4Statement Statement) -> Expr -> State P4State P4Statement
iteFromCascade t e (ECond _ [] d)                 = iteFromCascade t e d
iteFromCascade t e (ECond _ ((c,v):cs) d)         = do t' <- iteFromCascade t e v
                                                       e' <- iteFromCascade t e (ECond nopos cs d)
                                                       return $ P4SITE (printExpr c) t' $ Just e'
iteFromCascade (Left t) _ (EBool _ True)          = return t
iteFromCascade (Right t) _ (EBool _ True)         = mkStatement t
iteFromCascade _ Nothing (EBool _ False)          = return P4SNop
iteFromCascade _ (Just (Left e)) (EBool _ False)  = return e
iteFromCascade _ (Just (Right e)) (EBool _ False) = mkStatement e
iteFromCascade t e v                              = do t' <- case t of
                                                                  Left s  -> return s
                                                                  Right s -> mkStatement s
                                                       e' <- case e of 
                                                                  Nothing        -> return Nothing
                                                                  Just (Left s)  -> return $ Just s
                                                                  Just (Right s) -> liftM Just $ mkStatement s
                                                       return $ P4SITE (printExpr v) t' e'


-- convert expression into a cascade of ECond's, such
-- that their leaf expressions do not contain any EConds
liftConds :: (?r::Refine, ?c::ECtx, ?kmap::KMap) => Bool -> Expr -> Expr
liftConds todisj e = let ?todisj = (not $ exprNeedsTable e) && todisj
                     in evalExpr' $ liftConds' e

-- If e is a boolean expression, the cascade can be much more compactly
-- represented as a boolean expression.  However, this transformation 
-- introduces negations, which we cannot encode in P4 tables yet.  The ?todisj
-- flag signals when the transformation is safe, i.e., when its result is not
-- going to be programmed into a P4 table match entry.
liftConds' :: (?r::Refine, ?c::ECtx, ?kmap::KMap, ?todisj::Bool) => Expr -> Expr
liftConds' e = case typ' ?r ?c e' of
                    TBool _ -> if ?todisj 
                                  then cascadeToDisj e'
                                  else e'
                    _       -> e'
    where e' = liftConds'' e
                  
liftConds'' :: (?r::Refine, ?c::ECtx, ?kmap::KMap, ?todisj::Bool) => Expr -> Expr
liftConds'' e = 
    case e of 
         EVar _ _          -> e
         EDotVar _ _       -> e
         EPacket _         -> e
         EApply _ f as     -> combineCascades (EApply nopos f) $ map liftConds' as
         EBuiltin _ f as   -> combineCascades (EBuiltin nopos f) $ map liftConds' as
         EField _ s f      -> combineCascades (\[s'] -> EField nopos s' f) [liftConds' s]
         ELocation _ r as  -> combineCascades (ELocation nopos r) $ map liftConds' as
         EBool _ _         -> e
         EInt _ _ _        -> e
         EStruct _ s fs    -> EStruct nopos s $ map liftConds' fs
         EBinOp _ op e1 e2 -> combineCascades (\[e1', e2'] -> EBinOp nopos op e1' e2') [liftConds' e1, liftConds' e2]
         EUnOp _ op v      -> combineCascades (EUnOp nopos op . head) [liftConds' v]
         ESlice _ v h l    -> combineCascades (\[v'] -> ESlice nopos v' h l) [liftConds' v]
         ECond _ cs d      -> let d' = liftConds' d in
                              case d' of  
                                   ECond _ dcs dd -> ECond nopos ((map (\(c,v) -> (cascadeToDisj $ liftConds' c, liftConds' v)) cs)++dcs) dd
                                   _              -> ECond nopos (map (\(c,v) -> (cascadeToDisj $ liftConds' c, liftConds' v)) cs)        d'
    where combineCascades f es  = combineCascades' f es [] 
          combineCascades' f ((ECond _ cs d):es) es' = ECond nopos (map (mapSnd (\v -> combineCascades' f (v:es) es')) cs) (combineCascades' f (d:es) es')
          combineCascades' f (v:es) es'              = combineCascades' f es (es' ++ [v])
          combineCascades' f [] es'                  = f es'

-- XXX: this assumes that case conditions are mutually exclusive
cascadeToDisj :: Expr -> Expr
cascadeToDisj (ECond _ cs d) = disj $ (map (\(c,v) -> conj [cascadeToDisj c, cascadeToDisj v]) cs) ++ 
                                      [conj $ (map (EUnOp nopos Not . fst) cs) ++ [cascadeToDisj d]]
cascadeToDisj x              = x

mkAssignTable :: (?r::Refine, ?role::Role, ?kmap::KMap, ?pmap::PMap) => String -> Expr -> Expr -> State P4State ()
mkAssignTable n lhs rhs = do
    let actname = "a_" ++ n
        TUInt _ w = typ' ?r (CtxRole ?role) rhs 
        isdyn = exprNeedsTable rhs
        action = if isdyn
                    then (pp "action" <+> pp actname <> parens (pp "in" <+> pp ("bit<" ++ show w ++ ">") <+> pp "_val") <+> lbrace)
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
                 then [P4DynAction n ?role ?kmap rhs $ Just actname]
                 else []
        table = action
                $$
                (pp "table" <+> pp n <+> lbrace)
                $$
                (if isdyn 
                    then (nest' $ pp "reads" <+> (braces $ hsep $ map (\f -> printExpr f <> pp ": ternary" <> semi) matchFields)) 
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
 
mkCondTable :: (?r::Refine, ?role::Role, ?kmap::KMap, ?pmap::PMap) => String -> Expr -> State P4State ()
mkCondTable n e = do
    let table = (pp "table" <+> pp n <+> lbrace)
                $$
                (nest' $ pp "reads" <+> (braces $ hsep $ map (\f -> printExpr f <> pp ": ternary" <> semi) matchFields))
                $$
                (nest' $ pp "actions" <+> (braces $ pp "yes" <> semi <+> pp "no" <> semi))
                $$
                rbrace
--        command = pp "table_set_default" <+> pp n <+> pp "no"
        dyn = P4DynAction n ?role ?kmap e Nothing
    modify (\p4 -> p4{ p4Tables = p4Tables p4 ++ [table]
--                     , p4Commands = p4Commands p4 ++ [command]
                     , p4DynActions = p4DynActions p4 ++ [dyn]})

matchFields :: (?r::Refine, ?role::Role) => [Expr]
matchFields = fields (EPacket nopos) ++ [ingressPort] ++ (concatMap (fields . EVar nopos . name)$ roleLocals ?role)
    where fields e = case typ' ?r (CtxRole ?role) e of
                          TStruct _ fs -> concatMap (\f -> fields (EField nopos e $ name f)) 
                                          $ filter ((/= "valid") . name) fs
                          _            -> [e]

-----------------------------------------------------------------
-- Generate runtime updates to P4 tables
-----------------------------------------------------------------

populateTable :: Refine -> P4DynAction -> [Doc]
populateTable r P4DynAction{..} = 
    trace ("table " ++ p4dynTable) $
    case p4dynAction of
         Nothing -> mapIdx (\(msk,val) i -> case val of
                                                 EBool _ True  -> mkTableEntry p4dynTable "yes" [] msk i
                                                 EBool _ False -> mkTableEntry p4dynTable "no"  [] msk i
                                                 _             -> error $ "Non-constant boolean value " ++ show val) es
         Just a  -> mapIdx (\(msk,val) i -> mkTableEntry p4dynTable a [exprToVal val] msk i) es
    where es = let ?r = r
                   ?c = CtxRole p4dynRole
                   ?kmap = p4dynKMap in
               concatMap (\(c,v) -> map (,v) $ exprToMasks c) 
               $ flattenConds 
               $ liftConds False
               $ evalExpr' p4dynExpr

-- Flatten cascading cases into a sequence of (condition, value) pairs
-- in the order of decreasing priority.
flattenConds :: (?r::Refine, ?c::ECtx) => Expr -> [(Expr, Expr)]
flattenConds e = flattenConds' [] e

flattenConds' :: (?r::Refine, ?c::ECtx) => [Expr] -> Expr -> [(Expr, Expr)]
flattenConds' es (ECond _ cs d) = (concatMap (\(c,e) -> flattenConds' (es ++ [c]) e) cs) ++ (flattenConds' es d)
flattenConds' es e              = case typ' ?r ?c e of 
                                       TBool _ -> [ (conj $ es++[e], EBool nopos True)
                                                  , (conj es       , EBool nopos False)]
                                       _       -> [(conj es, e)]

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
exprToMasks :: (?r::Refine, ?c::ECtx, ?kmap::KMap) => Expr -> [Doc]
exprToMasks e = trace ("exprToMasks " ++ show e ++ " = " ++ show (map render res)) res
    where res = map disjunctToMask $ exprToDNF e

exprToDNF :: (?r::Refine, ?c::ECtx) => Expr -> [[Expr]]
exprToDNF (EBinOp _ And e1 e2) = concatMap (\d -> map (d++) $ exprToDNF e2) (exprToDNF e1)
exprToDNF (EBinOp _ Or e1 e2)  = exprToDNF e1 ++ exprToDNF e2
exprToDNF e@(EBinOp _ Eq e1 e2)  = 
    case typ' ?r ?c e1 of
         TStruct _ fs -> exprToDNF $ conj $ map (\f -> EBinOp nopos Eq (EField nopos e1 $ name f) (EField nopos e2 $ name f)) fs
         TUInt _ _    -> [[e]]
         _            -> error $ "Cannot convert expression " ++ show e ++ " to DNF" 
exprToDNF (EBool _ True) = [[]]
exprToDNF (EBool _ False) = []
exprToDNF e | (null $ exprFuncs ?r e) && ((product $ map (typeDomainSize ?r . typ ?r ?c) $ exprDeps e) <= maxExprTable) = 
        map fst $ filter ((==EBool nopos True) . snd) $ exprToTable e
exprToDNF e = error $ "Cannot convert expression " ++ show e ++ " to DNF" 

exprToTable :: (?r::Refine, ?c::ECtx) => Expr -> [([Expr], Expr)]
exprToTable e | null (exprDeps e) = [([], e)]
              | otherwise = let a = head $ exprDeps e
                                vals = typeEnumerate ?r $ typ ?r ?c a in 
                            concatMap (\v -> let vdnf = exprToDNF (EBinOp nopos Eq a v) in
                                             concatMap (\(es, eval) -> map ((, eval) . (++es)) vdnf) 
                                                       $ exprToTable $ evalExpr M.empty $ exprSubst a v e) vals

disjunctToMask :: (?r::Refine, ?c::ECtx, ?kmap::KMap) => [Expr] -> Doc
disjunctToMask atoms = mkMatch $ map (atomToMatch . evalExpr') atoms

-- maps atom of the form (x = const) to a (field_name, value)  
atomToMatch :: Expr -> (Expr, String)
atomToMatch e =
    case e of
         EBinOp _ Eq e1 (EInt _ _ i) -> (e1, "0x" ++ showHex i "")
         EBinOp _ Eq (EInt _ _ i) e2 -> (e2, "0x" ++ showHex i "")
         _                           -> error $ "Not implemented: P4.atomToMatch " ++ show e

-- Convert a list of (field,value) pairs into a P4 table match clause
-- by ordering the fields in the order required by the table and adding
-- don't care masks for all other fields.
mkMatch :: (?r::Refine, ?c::ECtx) => [(Expr,String)] -> Doc
mkMatch atoms = let CtxRole role = ?c in
                let ?role = role in 
                hsep $ map (\e -> let TUInt _ w = typ' ?r ?c e in
                                  case lookup e atoms of
                                       Nothing -> pp "0x0" <> pp "&&&" <> pp "0x0"
                                       Just v  -> pp v  <> pp "&&&" <> pp "0x" <> pp (showHex (mask w) "")) matchFields
    where mask w = foldl' (\a i -> setBit a i) (0::Integer) [0..w-1]

exprToVal :: Expr -> Doc
exprToVal (EInt _ _ i) = pp $ "0x" ++ showHex i ""
exprToVal e            = error $ "P4.exprToVal " ++ show e
