-- Convert NetKAT+ spec to P4

module P4() where

import Control.Monad.State

import PP

-- State maintained during compilation
data P4State = P4State { p4TableCnt :: Int   -- table counter
                       , p4Tables   :: [Doc] -- table specifications
                       , p4Commands :: [Doc] -- commands to go to the command file
                       }

data P4Statement = P4SSeq   P4Statement P4Statement
                 | P4SITE   Expr P4SITE (Maybe P4Statement)
                 | P4SApply String
                 | P4SDrop

data P4Action = P4AModify Expr Expr

incTableCnt :: State P4State Int
incTableCnt = do
    n <- gets p4TableCnt
    modify (\s -> s{p4TableCnt = n + 1})

--  Generate P4 switch. Returns to strings: one containing the P4 description
--  of the switch, and one containing runtime commands to initialize switch tables.
genP4Switch :: Refine -> Switch -> Store -> Store -> Store -> (Doc, Doc)
getP4Switch r switch fstore kstore pstore = 
    let ?r = r in
    let ?fstore = fstore in
    let ?kstore = kstore in
    let ?pstore = pstore in
    let (P4State _ tables command, controlstat) = runState (mkSwitch switch) (P4State 0 [] []) 
        control = (pp "control" <+> pp "ingress" <+> lbrace)
                  $$
                  controlstat
                  $$
                  rbrace
    in (pp "#include <parse.p4>" $$ pp "" $$ tables $$ pp "" $$ controlstat, vcat commands)

mkSwitch :: (?r::Refine, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Switch -> State P4State P4Statements
mkSwitch switch = do
    -- get the list of port numbers for each port group
    let portnums = map (\(port,_) -> sort $ M.keys (?pstore M.! port)) $ swPorts switch
    stats <- mapM (\(port,_) -> let ?role = getRole r port in mkStatement (roleBody ?role))
             $ swPorts switch
    let groups = filter (not . null . snd) $ zip stats portnums
    -- If there are multiple port groups, generate a top-level switch
    return $ foldl' (\st (st', pnums) -> let conds = map (\p -> EBinOp nopos Eq (EField nopos metadata "ingress_port") (EInt nopos p)) pnums
                                             cond = foldl' (\c c' -> EBinOp nopos Or c' c) (head conds) (tail conds)
                                         in P4SITE cond st' st) 
                    (fst $ head groups) (tail groups)

mkStatement :: (?r::Refine, ?role::Role, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Statement -> State P4State P4Statement
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
    return $ P4SITE (P4EUnOp Not e') P4SDrop Nothing

mkStatement (SSet  _ lhs rhs) = do
    tableid <- incTableCnt
    let tablename = "set" ++ show tableid
        lhs' = evalExpr lhs
        rhs' = evalExpr rhs
    mkSingleActionTable tablename (P4AModify lhs' rhs')
    return $ P4SApply tablename

mkStatement (SSend _ (ELocation _ n ks)) = do
    let dstgroup = getRole ?r n
        (EInt _ portnum) = evalExpr (last ks)
        egress = getPortNumber n portnum
    tableid <- incTableCnt
    let tablename = "send" ++ show tableid
    mkSingleActionTable tablename (P4AModify egressSpec (EInt nopos egress))
    return $ P4SApply tablename

mkSingleActionTable :: String -> P4Action -> State P4State ()
mkSingleActionTable n a = do
    let actname = "a_" ++ n
        table = (pp "action" <+> pp actname <> parens empty <+> lbrace)
                $$
                nest' $ mkAction a
                $$
                rbrace
                $$
                (pp "table" <+> n <+> lbrace) 
                $$
                (nest' $ pp "actions" <+> (braces $ pp actname)
                $$
                rbrace
        command = pp "table_set_default" <+> pp n <+> pp actname
    modify (\p4 -> p4{ p4Tables = p4Table p4 ++ [table]
                     , p4Commands = p4Commands p4 ++ [command]})
 

mkAction :: P4Action -> Doc
mkAction (P4AModify lhs rhs) = pp "modify_field" <> (parens $ printExpr lhs <> comma <+> printExpr rhs)

-- Partially evaluate expression
evalExpr  :: (?r::Refine, ?role::Role, ?fstore::Store, ?kstore::Store, ?pstore::Store) => Expr -> P4Expr
evalExpr (EKey _ k)                    = storeGetVal ?kstore k
evalExpr (EApply _ f [])               = evalExpr $ storeGetVal ?fstore f
evalExpr e@(EField _ s f)        = 
    case evalExpr s of
         EStruct _ _ fs -> let (TStruct _ sfs) = typ' ?r ?role s
                               fidx = findIndex ((== f) . name) sfs
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
            (EInt _ v1, EInt v2)     -> case op of
                                             Eq   -> EBool nopos (v1 == v2)
                                             Lt   -> EBool nopos (v1 < v2)
                                             Gt   -> EBool nopos (v1 > v2)
                                             Lte  -> EBool nopos (v1 <= v2)
                                             Gte  -> EBool nopos (v1 >= v2)
                                             Plus -> EInt  nopos ((v1 + v2) % (1 `shiftL` w))
                                             Mod  -> EInt  nopos (v1 % v2)
            _                        -> EBinOp op lhs' rhs'
evalExpr (EUnOp _ op e)                = 
    let e' = evalExpr e
    in case e' of
           (EBool _ v) -> case op of
                               Not -> EBool nopos (not v)
           _           -> EBool nopos e'
evalExpr (ECond _ cs d)                = 
    let cs' = map (\(e1,e2) -> (evalExpr e1, evalExpr e2)) cs
        cs'' = filter ((/= EBool nopos False) . fst) cs'
        d'  = evalExpr d
    in if null cs'' 
          then d'
          else if (fst $ head cs'') == (EBool nopos True)
                  then snd $ head cs''
                  else ECond nipos cs'' d'
evalExpr e                             = e
