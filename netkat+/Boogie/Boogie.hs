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
    (pp "/*" <+> pp asm <+> pp "*/")
    $$ 
    (pp "procedure" <+> pp "main" <+> parens empty <+> lbrace)
    $$
    (nest' body)
    $$
    rbrace
    where fs = exprFuncsRec conc $ assExpr asm
          concdef = all (isJust . funcDef . getFunc conc) fs
          abstdef = maybe False
                          (\abst -> all (maybe False (isJust . funcDef) . lookupFunc abst) fs)
                          mabst
          body = (vcat $ map ((<> semi) . mkField) $ assVars asm)
                 $$
                 (vcat $ map (\f -> pp "havoc" <+> (pp $ name f) <> semi) $ assVars asm)
                 $$
                 (pp "assert" <+> mkExpr conc (CtxAssume asm) (assExpr asm) <> semi)

type RMap = M.Map String String

refinementToBoogie1 :: Refine -> Refine -> String -> Doc
refinementToBoogie1 abst conc rname = vcat $ punctuate (pp "") [types, gvars, funcs, aroles, croles, assums, check]
    where tgts   = refineTarget conc
          new    = tgts ++ (map name (refineRoles conc) \\ map name (refineRoles abst))
          armap  = M.fromList $ map (\n -> (n, "a_" ++ n)) tgts
          crmap  = M.fromList $ map (\n -> (n, "c_" ++ n)) new
          types  = vcat $ (map mkTypeDef $ refineTypes conc) ++ [mkLocType conc, mkOutputType]
          gvars  = vcat $ [ var (pp "abs") (pp outputTypeName)
                          , var (pp "conc") (pp outputTypeName)
                          , var (pp "inppkt") (pp packetTypeName)]
          funcs  = vcat $ map (mkFunction conc) $ refineFuncs conc
          aroles = let ?rmap = armap 
                       ?ovar = "abs" in 
                   vcat $ punctuate (pp "") $ map (mkRole abst) $ refineRoles abst
          croles = let ?rmap = crmap 
                       ?ovar = "conc" in 
                   vcat $ punctuate (pp "") $ map (mkRole conc) $ refineRoles conc
          assums = vcat $ map (mkAssume conc) $ refineAssumes conc
          check  = mkCheck conc rname 

mkCheck :: Refine -> String -> Doc
mkCheck conc rname = (pp "procedure" <+> pp "main" <+> parens empty <+> lbrace)
                     $$
                     (nest' body)
                     $$
                     rbrace
    where role = getRole conc rname
          body = (vcat $ map ((<> semi) . mkField) $ roleKeys role)
                 $$
                 (vcat $ map (\f -> pp "havoc" <+> (pp $ name f) <> semi) $ roleKeys role)
                 $$
                 (pp "assume" <+> (mkExpr conc (CtxRole role) $ roleKeyRange role) <> semi)
                 $$
                 (pp "havoc" <+> pp "inppkt" <> semi)
                 $$
                 (pp "abs" =: pp "Dropped")
                 $$
                 (pp "conc" =: pp "Dropped")
                 $$
                 (vcat $ map mkField $ roleKeys role)
                 $$
                 (pp $ "a_" ++ rname)
                 $$
                 (pp "assert" <+> pp "abs" <+> pp "==" <+> pp "conc" <> semi)

mkLocType :: Refine -> Doc
mkLocType r = (pp "type" <+> pp "{:datatype}" <+> pp locTypeName <> semi)
              $$
              (vcat $ map mkLocConstructor $ refineRoles r)
              $$
              (pp "function" <+> pp "{:constructor}" <+> pp "Dropped" <> (parens $ empty) <> semi)

mkLocConstructor :: Role -> Doc
mkLocConstructor rl = pp "function" <+> pp "{:constructor}" <+> pp (name rl)
                   <> (parens $ hsep $ punctuate comma $ (map mkField $ roleKeys rl)) <> semi

mkOutputType :: Doc
mkOutputType = (pp "type" <+> pp "{:datatype}" <+> pp outputTypeName <> semi)
               $$
               (pp "function" <+> pp "{:constructor}" <+> pp outputTypeName
               <> (parens $ hsep $ punctuate comma $ [ pp "pkt" <> colon <+> pp packetTypeName
                                                     , pp "loc" <> colon <+> pp locTypeName])
               <> colon <+> pp outputTypeName <> semi)

mkRoleName :: (?rmap::RMap) => String -> Doc
mkRoleName n = case M.lookup n ?rmap of
                    Nothing -> pp n
                    Just n' -> pp n'

mkTypeDef :: TypeDef -> Doc
mkTypeDef TypeDef{..} = 
   case tdefType of
        TStruct   _ fs -> (pp "type" <+> pp "{:datatype}" <+> pp tdefName <> semi)
                          $$
                          (pp "function" <+> pp "{:constructor}" <+> pp tdefName       
                           <> (parens $ hsep $ punctuate comma $ map mkField fs) 
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
    where decl  = pp "function" <+> (pp $ name f) 
              <>  (parens $ hsep $ punctuate comma $ map mkField funcArgs)
              <> colon <+> (mkType funcType)

mkRole :: (?ovar::String, ?rmap::RMap) => Refine -> Role -> Doc
mkRole r rl@Role{..} = (pp "procedure" <+> mkRoleName roleName <+> (parens $ hsep $ punctuate comma args))
                       $$
                       (pp "requires" <+> mkExpr r (CtxRole rl) roleKeyRange <> semi)
                       $$
                       (pp "modifies" <+> pp ?ovar <> semi <> lbrace)
                       $$
                       (nest' $ mkStatement r rl roleBody)
                       $$
                       rbrace
    where args = map mkField $ roleKeys ++ [Field nopos pktVar $ tdefType $ getType r packetTypeName]

mkField :: Field -> Doc
mkField f = (pp $ name f) <> colon <+> (mkType $ fieldType f)

mkAssume :: Refine -> Assume -> Doc
mkAssume r a@Assume{..} = pp "axiom" <+> (parens $ pp "forall" <+> args <+> pp "::" <+> mkExpr r (CtxAssume a) assExpr) <> semi
    where args = hsep $ punctuate comma $ map mkField assVars

mkExpr :: Refine -> ECtx -> Expr -> Doc
mkExpr _ _ (EVar _ v)           = pp $ name v
mkExpr _ _ (EPacket _)          = pp pktVar
mkExpr r c (EApply _ f as)      = pp f <> (parens $ hsep $ punctuate comma $ map (mkExpr r c) as)
mkExpr r c (EField _ e f)       = let TUser _ tn = typ'' r c e
                                  in pp f <> char '#' <> pp tn <> (parens $ mkExpr r c e)
mkExpr _ _ (ELocation _ _ _)    = error "Not implemented: Boogie.mkExpr ELocation"
mkExpr _ _ (EBool _ True)       = pp "true"
mkExpr _ _ (EBool _ False)      = pp "false"
mkExpr _ _ (EInt _ w v)         = pp v <> text "bv" <> pp w
mkExpr r c (EStruct _ n fs)     = pp n <> (parens $ hsep $ punctuate comma $ map (mkExpr r c) fs)
mkExpr r c (EBinOp _ And e1 e2) = parens $ mkExpr r c e1 <+> text "&&" <+> mkExpr r c e2
mkExpr r c (EBinOp _ Or e1 e2)  = parens $ mkExpr r c e1 <+> text "||" <+> mkExpr r c e2
mkExpr r c (EBinOp _ op e1 e2)  = bvbop r c op e1 e2
mkExpr r c (EUnOp _ Not e)      = parens $ char '!' <> mkExpr r c e
mkExpr r c (ECond _ cs d)       = mkCond r c cs d 

mkCond r c [] d             = mkExpr r c d
mkCond r c ((cond, e):cs) d = parens $ pp "if" <> (parens $ mkExpr r c cond) <+> pp "then" <+> mkExpr r c e
                                                                             <+> pp "else" <+> mkCond r c cs d

bvbop r c op e1 e2 = text ("BV"++(show $ typeWidth $ typ' r c e1)++"_"++bvbopname op) <> (parens $ mkExpr r c e1 <> comma <+> mkExpr r c e2)

bvbopname Lt    = "ULT"
bvbopname Gt    = "UGT"
bvbopname Lte   = "ULEQ"
bvbopname Gte   = "UGEQ"
bvbopname And   = "AND"
bvbopname Or    = "OR"
bvbopname Plus  = "ADD"
bvbopname Minus = "SUB"
bvbopname op    = error $ "Not implemented: Boogie.bvbopname " ++ show op

mkStatement :: (?ovar::String, ?rmap::RMap) => Refine -> Role -> Statement -> Doc
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
mkStatement r _  (SSend _ dst)  = let ELocation _ rname ks = dst 
                                      rl' = getRole r rname in
                                  case M.lookup rname ?rmap of
                                       Nothing -> pp ?ovar =: (pp outputTypeName <> 
                                                               (parens $ pp pktVar <> comma <+>
                                                                        (pp rname <> (parens $ hsep $ punctuate comma $ map (mkExpr r (CtxRole rl')) ks))))
                                       Just _  -> mkRoleName rname <> (parens $ hsep $ punctuate comma 
                                                                       $ map (mkExpr r (CtxRole rl')) $ ks ++ [EPacket nopos]) <> semi

mkAssign :: Refine -> Role -> Expr -> [String] -> Expr -> Doc
mkAssign rf rl (EField _ e f) fs r = mkAssign rf rl e (fs ++ [f]) r
mkAssign rf rl l fs r              = mkExpr rf (CtxRole rl) l =: mkAssignRHS rf rl l fs r

mkAssignRHS :: Refine -> Role -> Expr -> [String] -> Expr -> Doc
mkAssignRHS rf rl _ []     r                = mkExpr rf (CtxRole rl) r
mkAssignRHS rf rl l (f:fs) r                = pp n <> (parens $ hsep $ punctuate comma 
                                                       $ map (\fn -> if' (fn == f) (mkAssignRHS rf rl l' fs r) (mkExpr rf (CtxRole rl) $ EField nopos l fn)) fns)
    where l' = EField nopos l f
          fns = map name $ typeFields $ typ' rf (CtxRole rl) l
          n = typeName $ typ'' rf (CtxRole rl) l

-- Boogie syntac helpers

(=:) :: Doc -> Doc -> Doc
(=:) l r = l <+> text ":=" <+> r <> semi

var :: Doc -> Doc -> Doc
var n t = pp "var" <+> n <> colon <+> t <> semi
