{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module Boogie.Boogie (refinementToBoogie) where

import Text.PrettyPrint
import qualified Data.Map as M
import Data.Maybe
import Data.List

import Syntax
import Name
import PP
import Type
import NS
import Pos
import Util
import Expr

outputTypeName = "_Output"
locTypeName    = "_Location"

outputVar = "_outp"
locationVar = "_loc"

refinementToBoogie :: Maybe Refine -> Refine -> ([(Assume, Doc)], Maybe [(String, Doc)])
refinementToBoogie mabst conc = (assums, roles)
    where assums = mapMaybe (\assm -> fmap (assm,) $ assumeToBoogie1 mabst conc assm) $ refineAssumes conc
          roles  = fmap (\abst -> map (\role -> (role, refinementToBoogie1 abst conc role)) $ refineTarget conc)
                        mabst

-- Generate verification condition to validate  an assumption.
-- Returns Nothing if not all functions involved in the assumption are defined
-- or if all of them were already defined in abst (in which case the 
-- assumption must have been validated during previous refinements).
assumeToBoogie1 :: Maybe Refine -> Refine -> Assume -> Maybe Doc
assumeToBoogie1 mabst conc asm | not concdef = Nothing
                               | abstdef     = Nothing
                               | otherwise   = Just $
    vcat $ punctuate (pp " ") $ 
    [ pp "/*" <+> pp asm <+> pp "*/"
    , mkBVOps conc
    , vcat $ (map mkTypeDef $ refineTypes conc) ++ [mkLocType conc]
    , vcat $ map (mkFunction conc . getFunc conc) fs
    , pp "procedure" <+> pp "main" <+> parens empty <+> lbrace
      $$
      (nest' body)
      $$
      rbrace]
    where fs = exprFuncsRec conc $ assExpr asm
          concdef = all (isJust . funcDef . getFunc conc) fs
          abstdef = maybe False
                          (\abst -> all (maybe False (isJust . funcDef) . lookupFunc abst) fs)
                          mabst
          body = (vcat $ map ((pp "var" <+>) . (<> semi) . mkField) $ assVars asm)
                 $$
                 (vcat $ map (havoc . pp . name) $ assVars asm)
                 $$
                 (assrt $ mkExpr conc (CtxAssume asm) (assExpr asm))

type RMap = M.Map String String

refinementToBoogie1 :: Refine -> Refine -> String -> Doc
refinementToBoogie1 abst conc rname = vcat $ punctuate (pp "") [ops, types, gvars, funcs, arole, croles, assums, check]
    where ops    = mkBVOps conc
          new    = rname : (map name (refineRoles conc) \\ map name (refineRoles abst))
          crmap  = M.fromList $ map (\n -> (n, "c_" ++ n)) new
          types  = vcat $ (map mkTypeDef $ refineTypes conc) ++ [mkLocType conc, mkOutputType]
          gvars  = vcat $ [var (pp outputVar) (pp outputTypeName)]
          funcs  = vcat $ map (mkFunction conc) $ refineFuncs conc
          arole  = mkAbstRole abst $ getRole abst rname
          croles = let ?rmap = crmap in 
                   vcat $ punctuate (pp "") $ map (mkConcRole conc) $ map (getRole conc) new
          assums = vcat $ map (mkAssume conc) $ refineAssumes conc
          check  = mkCheck conc rname 

mkCheck :: Refine -> String -> Doc
mkCheck conc rname = (pp "procedure" <+> pp "main" <+> parens empty)
                     $$
                     (modifies $ pp outputVar)
                     $$
                     lbrace
                     $$
                     (nest' body)
                     $$
                     rbrace
    where role = getRole conc rname
          body = (vcat $ map ((pp "var" <+>) . (<> semi) . mkField) $ roleKeys role)
                 $$
                 (var (pp "inppkt") (pp packetTypeName))
                 $$
                 (vcat $ map (havoc . pp . name) $ roleKeys role)
                 $$
                 (pp "assume" <+> (mkExpr conc (CtxRole role) $ roleKeyRange role) <> semi)
                 $$
                 (havoc (pp "inppkt"))
                 $$
                 (pp "assume" <+> (mkExprP "inppkt" conc (CtxRole role) $ rolePktGuard role) <> semi)
                 $$
                 (pp outputVar =: (pp "Dropped" <> (parens $ empty)))
                 $$
                 (call ("c_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt"])
                 $$
                 (call ("a_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt"])

mkLocType :: Refine -> Doc
mkLocType r = (pp "type" <+> pp "{:datatype}" <+> pp locTypeName <> semi)
              $$
              (vcat $ map mkLocConstructor $ refineRoles r)

mkLocConstructor :: Role -> Doc
mkLocConstructor rl = pp "function" <+> pp "{:constructor}" 
                   <+> (apply (name rl) $ map mkField $ roleKeys rl) 
                   <>  colon <+> pp locTypeName <> semi

mkOutputType :: Doc
mkOutputType = (pp "type" <+> pp "{:datatype}" <+> pp outputTypeName <> semi)
               $$
               (pp "function" <+> pp "{:constructor}" 
                <+> (apply outputTypeName $ [ pp "pkt" <> colon <+> pp packetTypeName
                                            , pp "loc" <> colon <+> pp locTypeName])
                <>  colon <+> pp outputTypeName <> semi)
               $$
               (pp "function" <+> pp "{:constructor}" <+> (apply "Dropped" []) <> colon <+> pp outputTypeName <> semi)

mkRoleName :: (?rmap::RMap) => String -> String
mkRoleName n = case M.lookup n ?rmap of
                    Nothing -> n
                    Just n' -> n'

mkTypeDef :: TypeDef -> Doc
mkTypeDef TypeDef{..} = 
   case tdefType of
        TStruct   _ fs -> (pp "type" <+> pp "{:datatype}" <+> pp tdefName <> semi)
                          $$
                          (pp "function" <+> pp "{:constructor}" <+> (apply tdefName $ map mkField fs) 
                           <> colon <+> pp tdefName <> semi)
        _              -> pp "type" <+> pp tdefName <+> char '=' <+> mkType tdefType <> semi
        
mkType :: Type -> Doc 
mkType (TLocation _) = error "Not implemented: Boogie.mkType TLocation"
mkType (TBool _)     = pp "bool"
mkType (TUInt _ w)   = pp "bv" <> pp w
mkType (TUser _ n)   = pp n
mkType t             = error $ "Boogie.mkType " ++ show t

mkFunction :: Refine -> Function -> Doc
mkFunction r f@Function{..} = maybe (decl <> semi) 
                                    (\e -> decl <+> lbrace $$ nest' (mkExpr r (CtxFunc f) e) $$ rbrace) 
                                    funcDef
    where decl = pp "function" <+> (apply (name f) $ map mkField funcArgs)
              <> colon <+> (mkType funcType)

mkAbstRole :: Refine -> Role -> Doc
mkAbstRole r rl@Role{..} = (pp "procedure" <+> (apply ("a_" ++ roleName) args))
                           $$
                           (pp "requires" <+> mkExpr r (CtxRole rl) roleKeyRange <> semi)
                           $$
                           (pp "requires" <+> mkExprP "_pkt" r (CtxRole rl) rolePktGuard <> semi)
                           $$
                           lbrace
                           $+$
                           (nest' $ mkAbstRoleBody r rl)
                           $$
                           rbrace
    where args = map mkField $ roleKeys ++ [Field nopos "_pkt" $ TUser nopos packetTypeName]



mkConcRole :: (?rmap::RMap) => Refine -> Role -> Doc
mkConcRole r rl@Role{..} = (pp "procedure" <+> (apply (mkRoleName roleName) args))
                           $$
                           (pp "requires" <+> mkExpr r (CtxRole rl) roleKeyRange <> semi)
                           $$
                           (pp "requires" <+> mkExprP "_pkt" r (CtxRole rl) rolePktGuard <> semi)
                           $$
                           (modifies $ pp outputVar)
                           $$
                           lbrace
                           $+$
                           (nest' $ var (pp locationVar) (pp locTypeName)
                                    $$
                                    var (pp pktVar) (pp packetTypeName) 
                                    $$
                                    pp pktVar =: pp "_pkt"
                                    $$
                                    mkStatement r rl roleBody)
                           $$
                           rbrace
    where args = map mkField $ roleKeys ++ [Field nopos "_pkt" $ TUser nopos packetTypeName]

mkField :: Field -> Doc
mkField f = (pp $ name f) <> colon <+> (mkType $ fieldType f)

mkAssume :: Refine -> Assume -> Doc
mkAssume r a@Assume{..} = pp "axiom" <+> (parens $ pp "forall" <+> args <+> pp "::" <+> mkExpr r (CtxAssume a) assExpr) <> semi
    where args = hsep $ punctuate comma $ map mkField assVars

mkExpr :: Refine -> ECtx -> Expr -> Doc
mkExpr r c e = mkExprP pktVar r c e

-- Set of modified fields. Includes expressions of the form pkt.f1.f2.....fn
type MSet = [Expr]

mkAbstExpr :: (?r::Refine) => ECtx -> MSet -> Expr -> Doc
mkAbstExpr c mset e = let ?mset = mset 
                          ?c = c
                          ?loc = apply ("loc#" ++ outputTypeName) [pp outputVar]
                          ?p = "_pkt" in 
                      mkExpr' e

mkExprP :: String -> Refine -> ECtx -> Expr -> Doc
mkExprP p r c e = let ?c = c
                      ?p = p 
                      ?r = r 
                      ?loc = apply ("loc#" ++ outputTypeName) [pp outputVar]
                      ?mset = [] in
                  mkExpr' e

-- Generage Boogie expression.
-- Replace packet fields in ?mset with field of outputVar
mkExpr' :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx, ?loc::Doc) => Expr -> Doc
mkExpr' (EVar _ v)           = pp v
mkExpr' (EDotVar _ v)        = let CtxSend _ rl = ?c in 
                               apply (v ++ "#" ++ (name rl)) [?loc]
mkExpr' e@(EPacket _)        = mkPktField e
mkExpr' (EApply _ f as)      = apply f $ map mkExpr' as
mkExpr' e@(EField _ s f) | isPktField s = mkPktField e
                         | otherwise    = 
                               let TUser _ tn = typ'' ?r ?c s
                               in pp f <> char '#' <> pp tn <> (parens $ mkExpr' s)
    where isPktField (EField _ s' _) = isPktField s'
          isPktField (EPacket _)     = True
          isPktField _               = False
mkExpr' (ELocation _ _ _)    = error "Not implemented: Boogie.mkExpr' ELocation"
mkExpr' (EBool _ True)       = pp "true"
mkExpr' (EBool _ False)      = pp "false"
mkExpr' (EInt _ w v)         = pp v <> text "bv" <> pp w
mkExpr' (EStruct _ n fs)     = apply n $ map mkExpr' fs
mkExpr' (EBinOp _ Eq e1 e2)  = parens $ mkExpr' e1 === mkExpr' e2
mkExpr' (EBinOp _ And e1 e2) = parens $ mkExpr' e1 &&& mkExpr' e2
mkExpr' (EBinOp _ Or e1 e2)  = parens $ mkExpr' e1 ||| mkExpr' e2
mkExpr' (EBinOp _ op e1 e2)  = bvbop op e1 e2
mkExpr' (EUnOp _ Not e)      = parens $ char '!' <> mkExpr' e
mkExpr' (ECond _ cs d)       = mkCond cs d 

mkPktField :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx) => Expr -> Doc
mkPktField e = 
    -- Parent or e in mset -- outp.field
    if isInMSet e
       then field (apply ("pkt#" ++ outputTypeName) [pp outputVar]) e
       else if not (overlapsMSet e ?mset)
               then -- None of the children overlaps with mset -- generate as is
                    field (pp ?p) e
               else -- otherwise -- constructor with recursive calls for fields
                    let TUser _ tn = typ'' ?r ?c e
                        TStruct _ fs = typ' ?r ?c e in
                    (apply tn $ map (mkPktField . EField nopos e . name) fs)
    where isInMSet x = elem x ?mset ||
                       case x of
                            EField _ p _ -> isInMSet p
                            _            -> False
          field p (EPacket _)    = p
          field p (EField _ s f) = let TUser _ tn = typ'' ?r ?c s
                                   in pp f <> char '#' <> pp tn <> (parens $ field p s)
          field _ e'             = error $ "Boogie.mkPktField.field " ++ show e'


mkCond :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx, ?loc::Doc) => [(Expr,Expr)] -> Expr -> Doc
mkCond [] d             = mkExpr' d
mkCond ((cond, e):cs) d = parens $ pp "if" <> (parens $ mkExpr' cond) <+> pp "then" <+> mkExpr' e
                                                                      <+> pp "else" <+> mkCond cs d

bvbop :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx, ?loc::Doc) => BOp -> Expr -> Expr -> Doc
bvbop op e1 e2 = text ("BV"++(show $ typeWidth $ typ' ?r ?c e1)++"_"++bvbopname op) <> (parens $ mkExpr' e1 <> comma <+> mkExpr' e2)

bvbopname Lt    = "ULT"
bvbopname Gt    = "UGT"
bvbopname Lte   = "ULEQ"
bvbopname Gte   = "UGEQ"
bvbopname And   = "AND"
bvbopname Or    = "OR"
bvbopname Plus  = "ADD"
bvbopname Minus = "SUB"
bvbopname op    = error $ "Not implemented: Boogie.bvbopname " ++ show op

mkStatement :: (?rmap::RMap) => Refine -> Role -> Statement -> Doc
mkStatement r rl (SSeq _ s1 s2) = mkStatement r rl s1 $$ mkStatement r rl s2
mkStatement _ _  (SPar _ _ _)   = error "Not implemented: Boogie.mkStatement SPar" {- run in sequence, copying packet -}
mkStatement r rl (SITE _ c t e) = (pp "if" <> (parens $ mkExpr r (CtxRole rl) c) <+> lbrace)
                                  $$
                                  (nest' $ mkStatement r rl t)
                                  $$
                                  (maybe rbrace
                                         (\s -> (rbrace <+> pp "else" <+> lbrace) 
                                                $$
                                                (nest' $ mkStatement r rl s)
                                                $$
                                                rbrace)
                                         e)
mkStatement r rl (STest _ c)    = pp "if" <> (parens $ mkExpr r (CtxRole rl) (EUnOp nopos Not c)) <+> (braces $ pp "return" <> semi)
mkStatement r rl (SSet _ l rhs) = mkAssign r rl l [] rhs
mkStatement r rl (SSend _ dst)  = let ELocation _ rname ks = dst in
                                  case M.lookup rname ?rmap of
                                       Nothing -> pp outputVar =: (pp outputTypeName <> 
                                                                   (parens $ pp pktVar <> comma <+>
                                                                             (apply rname $ map (mkExpr r (CtxRole rl)) ks)))
                                       Just _  -> call (mkRoleName rname) $ map (mkExpr r (CtxRole rl)) $ ks ++ [EPacket nopos]
mkStatement r rl (SSendND _ n c) = let rl' = getRole r n in
                                   case M.lookup n ?rmap of
                                        Nothing -> (havoc $ pp outputVar)
                                                   $$
                                                   assume notDropped
                                                   $$
                                                   (assume $ apply ("is#" ++ n) [apply ("loc#" ++ outputTypeName) [pp outputVar]])
                                                   $$
                                                   (assume $ mkExpr r (CtxSend rl rl') c)
                                        Just _  -> (havoc $ pp locationVar)
                                                   $$
                                                   (assume $ apply ("is#" ++ n) [pp locationVar])
                                                   $$
                                                   (assume $ let ?p = pktVar
                                                                 ?mset = []
                                                                 ?r = r
                                                                 ?c = CtxSend rl rl'
                                                                 ?loc = pp locationVar in
                                                             mkExpr' c)
                                                   $$
                                                   (call (mkRoleName n) 
                                                         $ (map (\k -> apply (name k ++ "#" ++ n) [pp locationVar]) $ roleKeys rl') ++ [pp pktVar])
mkStatement r rl (SHavoc _ e)    = havoc $ mkExpr r (CtxRole rl) e
mkStatement r rl (SAssume _ e)   = assume $ mkExpr r (CtxRole rl) e

mkAssign :: Refine -> Role -> Expr -> [String] -> Expr -> Doc
mkAssign rf rl (EField _ e f) fs r = mkAssign rf rl e (f:fs) r
mkAssign rf rl l fs r              = mkExpr rf (CtxRole rl) l =: mkAssignRHS rf rl l fs r

mkAssignRHS :: Refine -> Role -> Expr -> [String] -> Expr -> Doc
mkAssignRHS rf rl _ []     r                = mkExpr rf (CtxRole rl) r
mkAssignRHS rf rl l (f:fs) r                = apply n $ map (\fn -> if' (fn == f) (mkAssignRHS rf rl l' fs r) (mkExpr rf (CtxRole rl) $ EField nopos l fn)) fns
    where l' = EField nopos l f
          fns = map name $ typeFields $ typ' rf (CtxRole rl) l
          n = typeName $ typ'' rf (CtxRole rl) l

mkAbstRoleBody :: Refine -> Role -> Doc
mkAbstRoleBody r rl = 
    (let ?r = r
         ?rl = rl in
     mkAbstStatement [] [] $ roleBody rl)
    $$
    checkDropped

mkAbstStatement :: (?r::Refine, ?rl::Role) => MSet -> [Statement] -> Statement -> Doc
mkAbstStatement mset nxt (SSeq _ s1 s2) = mkAbstStatement mset (s2:nxt) s1
mkAbstStatement _    _   (SPar _ _ _)   = error "Not implemented: Boogie.mkAbstStatement SPar" {- run in sequence, copying packet -}
mkAbstStatement mset nxt (SITE _ c t e) = stat
    where clone = (isNothing $ statMSet t) || (statMSet t /= maybe (Just []) statMSet e)
          tbranch = if clone
                       then mkAbstStatement mset nxt t
                       else mkAbstStatement mset []  t
          ebranch = if clone
                       then mkAbstStatement mset nxt $ fromJust e
                       else mkAbstStatement mset []  $ fromJust e
          suffix = if clone 
                      then empty
                      else mkNext (msetUnion mset $ fromJust $ statMSet t) nxt
          stat = (pp "if" <> (parens $ mkAbstExpr (CtxRole ?rl) mset c) <+> lbrace)
                 $$
                 (nest' tbranch)
                 $$
                 (maybe rbrace
                        (\_ -> (rbrace <+> pp "else" <+> lbrace) 
                               $$
                               (nest' ebranch)
                               $$
                               rbrace)
                        e)
                 $$
                 suffix
mkAbstStatement mset nxt (STest _ c)    = pp "if" <> (parens $ mkAbstExpr (CtxRole ?rl) mset (EUnOp nopos Not c)) <+> (braces $ checkDropped <+> ret)
                                          $$
                                          mkNext mset nxt
mkAbstStatement mset nxt (SSet _ l rhs) = (assrt $ isDropped ||| (parens $ mkAbstExpr (CtxRole ?rl) mset' l === mkAbstExpr (CtxRole ?rl) mset rhs))
                                          $$
                                          mkNext mset' nxt
    where mset' = msetUnion [l] mset
mkAbstStatement mset []  (SSend _ dst)  = checkNotDropped
                                          $$
                                          (assrt $ (apply ("loc#" ++ outputTypeName) [pp outputVar]) === (apply rname $ map (mkAbstExpr (CtxRole ?rl) mset) ks))
                                          $$
                                          (vcat $ map (\e -> assrt $ mkAbstExpr (CtxRole ?rl) mset' e === mkAbstExpr (CtxRole ?rl) mset e) mset')
                                          $$
                                          ret
    where mset' = msetComplement mset
          ELocation _ rname ks = dst
mkAbstStatement mset []  (SSendND _ rl c) = checkNotDropped
                                            $$
                                            (assrt $ apply ("is#" ++ rl) [apply ("loc#" ++ outputTypeName) [pp outputVar]])
                                            $$
                                            (assrt $ mkAbstExpr (CtxSend ?rl $ getRole ?r rl) mset c)
                                            $$
                                            (vcat $ map (\e -> assrt $ mkAbstExpr (CtxRole ?rl) mset' e === mkAbstExpr (CtxRole ?rl) mset e) mset')
                                            $$
                                            ret
    where mset' = msetComplement mset
mkAbstStatement mset nxt (SHavoc _ e)   = mkNext (msetUnion mset [e]) nxt
mkAbstStatement mset nxt (SAssume _ c)  = (assrt $ isDropped ||| mkAbstExpr (CtxRole ?rl) mset c)
                                          $$
                                          mkNext mset nxt
mkAbstStatement _    nxt s              = error $ "Boogie.mkAbstStatement " ++ show nxt ++ " " ++ show s

isDropped :: Doc
isDropped = apply "is#Dropped" [pp outputVar]

notDropped :: Doc
notDropped = apply "!is#Dropped" [pp outputVar]

checkDropped :: Doc
checkDropped = assrt isDropped

checkNotDropped :: Doc
checkNotDropped = assrt notDropped

mkNext :: (?r::Refine, ?rl::Role) => MSet -> [Statement] -> Doc
mkNext mset nxt = case nxt of
                       []     -> empty
                       (s:ss) -> mkAbstStatement mset ss s

statMSet :: Statement -> Maybe MSet
statMSet (SSeq _ l r)    = maybe Nothing (\mset -> maybe Nothing (Just . msetUnion mset) $ statMSet r) $ statMSet l
statMSet (SPar _ _ _)    = error "Boogie.statMSet SPar"
statMSet (SITE _ _ t me) = maybe Nothing 
                                 (\msett -> maybe Nothing 
                                                  (\msete -> if' (msetEq msete msett) (Just msete) Nothing) 
                                                  (maybe (Just []) statMSet me)) 
                                 (statMSet t)
statMSet (STest _ _)     = Just []
statMSet (SSet _ l _)    = Just [l]
statMSet (SSend  _ _)    = Nothing
statMSet (SSendND _ _ _) = Nothing
statMSet (SHavoc _ l)    = Just [l]
statMSet (SAssume _ _)   = Just []

msetEq :: MSet -> MSet -> Bool
msetEq ms1 ms2 = length ms1 == length ms2 && (length $ intersect ms1 ms2) == length ms1

-- assumes non-overlapping sets
msetUnion :: MSet -> MSet -> MSet
msetUnion s1 s2 = union s1 s2

overlapsMSet :: (?r::Refine, ?c::ECtx) => Expr -> MSet -> Bool
overlapsMSet x mset = elem x mset ||
                      case typ' ?r ?c x of
                           TStruct _ fs -> any (\f -> overlapsMSet (EField nopos x $ name f) mset) fs
                           _            -> False 


msetComplement :: (?r::Refine, ?rl::Role) => MSet -> MSet
msetComplement mset = msetComplement' (EPacket nopos)
    where ctx = CtxRole ?rl
          msetComplement' e = if elem e mset
                                 then []
                                 else if (let ?c = ctx in overlapsMSet e mset)
                                         then let TStruct _ fs = typ' ?r ctx e in
                                              concatMap (msetComplement' . EField nopos e . name) fs
                                         else [e]

mkBVOps :: Refine -> Doc
mkBVOps r = vcat $ map mkOpDecl $ collectOps r

mkOpDecl :: (Either UOp BOp, Int) -> Doc
mkOpDecl (Right Lt   , w) = mkBOpDecl "bvult" (bvbopname Lt)    w "bool" 
mkOpDecl (Right Gt   , w) = mkBOpDecl "bvugt" (bvbopname Gt)    w "bool" 
mkOpDecl (Right Lte  , w) = mkBOpDecl "bvule" (bvbopname Lte)   w "bool" 
mkOpDecl (Right Gte  , w) = mkBOpDecl "bvuge" (bvbopname Gte)   w "bool" 
mkOpDecl (Right Plus , w) = mkBOpDecl "bvadd" (bvbopname Plus)  w (bvtname w)
mkOpDecl (Right Minus, w) = mkBOpDecl "bvsub" (bvbopname Minus) w (bvtname w)
mkOpDecl _                = empty

mkBOpDecl builtin opname w retname = pp $ "function {:bvbuiltin \"" ++ builtin ++ "\"} BV" ++ show w ++ "_" ++ opname ++ "(x:" ++ bvtname w ++ ", " ++ "y:" ++ bvtname w ++ ")" ++ " returns (" ++ retname ++ ");"
bvtname w = "bv" ++ show w


collectOps :: Refine -> [(Either UOp BOp, Int)]
collectOps r@Refine{..} = let ?r = r in
                          nub $ concatMap (\f -> maybe [] (exprCollectOps (CtxFunc f)) $ funcDef f) refineFuncs ++
                                concatMap (\a -> exprCollectOps (CtxAssume a) $ assExpr a) refineAssumes ++
                                concatMap (\rl -> exprCollectOps (CtxRole rl) $ roleKeyRange rl) refineRoles ++
                                concatMap (\rl -> exprCollectOps (CtxRole rl) $ rolePktGuard rl) refineRoles ++
                                concatMap (\rl -> statCollectOps rl $ roleBody rl) refineRoles

statCollectOps :: (?r::Refine) => Role -> Statement -> [(Either UOp BOp, Int)]
statCollectOps rl (SSeq _ l r)    = statCollectOps rl l ++ statCollectOps rl r
statCollectOps rl (SPar  _ l r)   = statCollectOps rl l ++ statCollectOps rl r
statCollectOps rl (SITE _ c t me) = exprCollectOps (CtxRole rl) c ++ statCollectOps rl t ++ maybe [] (statCollectOps rl) me
statCollectOps rl (STest _ c)     = exprCollectOps (CtxRole rl) c
statCollectOps rl (SSet _ l r)    = exprCollectOps (CtxRole rl) l ++ exprCollectOps (CtxRole rl) r
statCollectOps rl (SSend _ d)     = exprCollectOps (CtxRole rl) d
statCollectOps rl (SSendND _ n c) = exprCollectOps (CtxSend rl $ getRole ?r n) c
statCollectOps _  (SHavoc _ _)    = []
statCollectOps rl (SAssume _ c)   = exprCollectOps (CtxRole rl) c

exprCollectOps :: (?r::Refine) => ECtx -> Expr -> [(Either UOp BOp, Int)]
exprCollectOps c (EApply _ _ as)    = concatMap (exprCollectOps c) as
exprCollectOps c (EField _ s _)     = exprCollectOps c s
exprCollectOps c (ELocation _ _ as) = concatMap (exprCollectOps c) as
exprCollectOps c (EStruct _ _ fs)   = concatMap (exprCollectOps c) fs
exprCollectOps c (EBinOp _ op l r)  = (exprCollectOps c l ++ exprCollectOps c r) ++ 
                                      case typ' ?r c l of
                                            TUInt _ w -> [(Right op, w)]
                                            _         -> []
exprCollectOps c (EUnOp _ _ e)      = exprCollectOps c e
exprCollectOps c (ECond _ cs d)     = concatMap (\(e, v) -> exprCollectOps c e ++ exprCollectOps c v) cs ++ exprCollectOps c d
exprCollectOps _ _ = []

-- Boogie syntax helpers

(=:) :: Doc -> Doc -> Doc
(=:) l r = l <+> text ":=" <+> r <> semi

var :: Doc -> Doc -> Doc
var n t = pp "var" <+> n <> colon <+> t <> semi

modifies :: Doc -> Doc
modifies v = pp "modifies" <+> v <> semi

assrt :: Doc -> Doc
assrt c = pp "assert" <+> c <> semi

assume :: Doc -> Doc
assume c = pp "assume" <+> c <> semi

(===) :: Doc -> Doc -> Doc
(===) x y = x <+> pp "==" <+> y

(|||) :: Doc -> Doc -> Doc
(|||) x y = x <+> pp "||" <+> y

(&&&) :: Doc -> Doc -> Doc
(&&&) x y = x <+> pp "&&" <+> y

apply :: String -> [Doc] -> Doc
apply f as = pp f <> (parens $ hsep $ punctuate comma as)

call :: String -> [Doc] -> Doc
call f as = pp "call" <+> apply f as <> semi

havoc :: Doc -> Doc
havoc x = pp "havoc" <+> x <> semi

ret :: Doc
ret = pp "return" <> semi
