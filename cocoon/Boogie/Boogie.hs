{-# LANGUAGE ImplicitParams, RecordWildCards, TupleSections #-}

module Boogie.Boogie (refinementToBoogie) where

import Text.PrettyPrint
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.String.Utils

import Syntax
import Name
import PP
import Type
import NS
import Pos
import Util
import Expr
import Refine
import Boogie.BoogieHelpers
import Boogie.BoogieExpr

boogieHeader = pp $ 
    "function _div(x: int, y: int): int;\n" ++
    "axiom (forall x: int, y: int :: ((y>0) && (x>=0)) ==> ((_div(x,y) <= x) && (_div(x,y)>=0)));\n" ++
    "function _mod(x: int, y: int): int;\n" ++
    "axiom (forall x: int, y: int :: ((y>0) && (x>=0) ) ==> ((_mod(x,y) <= x) && (_mod(x,y) < y) && (_mod(x,y)>=0)));\n" ++
    "function _slice(x: int, h: int, l: int, m: int): int;\n" ++
    "axiom (forall x: int, h: int, l: int, m: int :: (m>0) ==> ((_slice(x,h,l,m) < m) && (_slice(x,h,l,m)>=0)));\n" ++
    "function _concat(x: int, y: int, m: int): int;\n" ++
    "axiom (forall x: int, y: int, m: int :: (m>0) ==> ((_concat(x,y,m) < m) && (_concat(x,y,m)>=0)));\n"

data Encoding = EncAsProcedure
              | EncAsFunction
              | EncAsFunctionReverse
              deriving (Eq)

refinementToBoogie :: Maybe Refine -> Refine -> Int -> ([(Assume, Doc)], Maybe [(String, Doc)])
refinementToBoogie mabst conc maxdepth = (assums, roles)
    where assums = mapMaybe (\assm -> fmap (assm,) $ assumeToBoogie1 mabst conc assm) $ refineAssumes conc
          roles  = fmap (\abst -> concatMap (\role -> if refineIsMulticast Nothing abst role
                                                         then [ (role, refinementToBoogie1 EncAsFunction abst conc role maxdepth)
                                                              , ("_" ++ role, refinementToBoogie1 EncAsFunctionReverse abst conc role maxdepth)]
                                                         else [{-(role, refinementToBoogie1  abst conc role maxdepth)-}
                                                               (role, refinementToBoogie1 EncAsFunction abst conc role maxdepth)])
                                            $ refineTarget conc)
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
--    , mkBVOps conc
    , boogieHeader
    , mkBoundsCheckers conc
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
                 (vcat $ map (\v -> havoc' conc (pp $ name v, fieldType v)) $ assVars asm)
                 $$
                 (assrt $ mkExpr conc (CtxAssume asm) (assExpr asm))

type RMap = M.Map String String

refinementToBoogie1 :: Encoding -> Refine -> Refine -> String -> Int -> Doc
refinementToBoogie1 enc abst conc rname maxdepth = vcat $ punctuate (pp "") [{-ops,-} boogieHeader, bounds, types, gvars, funcs, roles, assums, check]
    where --ops    = mkBVOps conc
          bounds = mkBoundsCheckers conc
          new    = rname : (map name (refineRoles conc) \\ map name (refineRoles abst))
          crmap  = M.fromList $ map (\n -> (n, "c_" ++ n)) new
          types  = vcat $ (map mkTypeDef $ refineTypes conc) ++ [mkLocType conc, mkOutputType]
          gvars  = vcat $ [ var (pp outputVar) (pp outputTypeName)
                          , var (pp depthVar) (pp "int")]
          funcs  = vcat $ map (mkFunction conc) $ refineFuncs conc
          roles  = let ?maxdepth = maxdepth in
                   case enc of 
                        EncAsProcedure -> (mkAbstRole abst $ getRole abst rname)
                                          $$
                                          (let ?rmap = crmap in 
                                           vcat $ punctuate (pp "") $ map (mkRoleAsProc conc) $ map (getRole conc) new)
                        EncAsFunction  -> (let ?rmap = M.singleton rname ("a_" ++ rname) in
                                           mkRoleAsFunction abst $ getRole abst rname)
                                          $$
                                          (let ?rmap = crmap in
                                           vcat $ punctuate (pp "") $ map (mkRoleAsProc conc) $ map (getRole conc) new)
                        EncAsFunctionReverse -> (let ?rmap = crmap in
                                                 vcat $ map (mkRoleAsFunction conc . getRole conc) new)
                                                $$
                                                (let ?rmap = M.singleton rname ("a_" ++ rname) in
                                                 mkRoleAsProc abst $ getRole abst rname)
          assums = vcat $ map (mkAssume conc) $ refineAssumes conc
          check  = mkCheck enc conc rname 


mkCheck :: Encoding -> Refine -> String -> Doc
mkCheck enc conc rname = (pp "procedure" <+> pp "main" <+> parens empty)
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
                 (vcat $ map (\k -> havoc' conc (pp $ name k, fieldType k)) $ roleKeys role)
                 $$
                 (pp "assume" <+> (mkExpr conc (CtxRole role) $ roleKeyRange role) <> semi)
                 $$
                 (havoc' conc (pp "inppkt", TUser nopos packetTypeName))
                 $$
                 (pp "assume" <+> (mkExprP "inppkt" conc (CtxRole role) $ rolePktGuard role) <> semi)
                 $$
                 (pp outputVar .:= (pp "Dropped" <> (parens $ empty)))
                 $$
                 (pp depthVar .:= pp "0")
                 $$
                 (if enc == EncAsFunctionReverse 
                     then call ("a_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt"]
                     else call ("c_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt"])
                 $$
                 case enc of
                      EncAsProcedure       -> call ("a_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt"]
                      EncAsFunction        -> assrt $ apply ("a_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt", pp outputVar]
                      EncAsFunctionReverse -> assrt $ apply ("c_" ++ rname) $ (map (pp . name) $ roleKeys role) ++ [pp "inppkt", pp outputVar]

mkLocType :: Refine -> Doc
mkLocType r = (pp "type" <+> pp "{:datatype}" <+> pp locTypeName <> semi)
              $$
              (vcat $ map mkLocConstructor $ refineRoles r)

mkLocConstructor :: Role -> Doc
mkLocConstructor rl = pp "function" <+> pp "{:constructor}" 
                   <+> (apply (name rl) $ map mkField $ roleKeys rl) 
                   .: pp locTypeName <> semi

mkOutputType :: Doc
mkOutputType = (pp "type" <+> pp "{:datatype}" <+> pp outputTypeName <> semi)
               $$
               (pp "function" <+> pp "{:constructor}" 
                <+> (apply outputTypeName $ [ pp "pkt" .: pp packetTypeName
                                            , pp "loc" .: pp locTypeName])
                .: pp outputTypeName <> semi)
               $$
               (pp "function" <+> pp "{:constructor}" <+> (apply "Dropped" []) .: pp outputTypeName <> semi)

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
                           .: pp tdefName <> semi)
        _              -> pp "type" <+> pp tdefName <+> char '=' <+> mkType tdefType <> semi
        
mkType :: Type -> Doc 
mkType (TLocation _) = error "Not implemented: Boogie.mkType TLocation"
mkType (TBool _)     = pp "bool"
mkType (TUInt _ _)   = pp "int" -- pp "bv" <> pp w
mkType (TUser _ n)   = pp n
mkType t             = error $ "Boogie.mkType " ++ show t

mkFunction :: Refine -> Function -> Doc
mkFunction r f@Function{..} = maybe ((decl <> semi)
                                     $$
                                     (if isUInt r undefined funcType || isStruct r undefined funcType then asm else empty))
                                    (\e -> decl <+> lbrace $$ nest' (mkExpr r (CtxFunc f) e) $$ rbrace) 
                                    funcDef
    where decl = pp "function" <+> (apply (name f) $ map mkField funcArgs)
              .: (mkType funcType)
          -- Values returned by uninterpreted functions are within their type bounds
          asm = axiom (map (\a -> mkField $ Field nopos (name a) (fieldType a)) funcArgs) asmbody
          bexpr = apply (name f) $ map (pp . name) funcArgs
          asmbody = checkBVBounds r [(bexpr, funcType)]

mkRoleAsFunction :: (?rmap::RMap) => Refine -> Role -> Doc
mkRoleAsFunction r rl@Role{..} = (pp "function" <+> (apply (mkRoleName roleName) args) <> pp ":" <+> pp "bool" <+> lbrace)
                                 $$
                                 (nest' $ let ?r = r in mkRoleFuncBody rl)
                                 $$
                                 rbrace
    where args = (map mkField roleKeys) ++ [pp "_pkt" .: pp packetTypeName, pp outputVar .: pp outputTypeName]
 
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



mkRoleAsProc :: (?rmap::RMap, ?maxdepth::Int) => Refine -> Role -> Doc
mkRoleAsProc r rl@Role{..} = (pp "procedure" <+> (apply (mkRoleName roleName) args))
                             $$
                             (pp "requires" <+> mkExpr r (CtxRole rl) roleKeyRange <> semi)
                             $$
                             (pp "requires" <+> mkExprP "_pkt" r (CtxRole rl) rolePktGuard <> semi)
                             $$
                             (pp "requires" <+> checkBVBounds r (map (\k -> (pp $ name k, fieldType k)) roleKeys) <> semi)
                             $$
                             (modifies $ pp outputVar)
                             $$
                             lbrace
                             $+$
                             (nest' $ var (pp locationVar) (pp locTypeName)
                                      $$
                                      var (pp pktVar) (pp packetTypeName) 
                                      $$
                                      (vcat $ map ((pp "var" <+>) . (<> semi) . mkField) $ roleLocals rl)
                                      $$
                                      (vcat $ map ((pp "var" <+>) . (<> semi) . mkField) $ roleForkVars rl)
                                      $$
                                      pp pktVar .:= pp "_pkt"
                                      $$
                                      mkStatement r (CtxRole rl) roleBody)
                             $$
                             rbrace
    where args = map mkField $ roleKeys ++ [Field nopos "_pkt" $ TUser nopos packetTypeName]

mkField :: Field -> Doc
mkField f = (pp $ name f) .: (mkType $ fieldType f)

mkAssume :: Refine -> Assume -> Doc
mkAssume r a@Assume{..} = axiom (map mkField assVars) (mkExpr r (CtxAssume a) assExpr)

--bvbop :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx, ?loc::Doc) => BOp -> Expr -> Expr -> Doc
--bvbop op e1 e2 = text ("BV"++(show $ typeWidth $ typ' ?r ?c e1)++"_"++bvbopname op) <> (parens $ mkExpr' e1 <> comma <+> mkExpr' e2)

--bvbopname Lt    = "ULT"
--bvbopname Gt    = "UGT"
--bvbopname Lte   = "ULEQ"
--bvbopname Gte   = "UGEQ"
--bvbopname Plus  = "ADD"
--bvbopname Minus = "SUB"
--bvbopname op    = error $ "Not implemented: Boogie.bvbopname " ++ show op

mkStatement :: (?rmap::RMap, ?maxdepth::Int) => Refine -> ECtx -> Statement -> Doc
mkStatement r ctx (SSeq _ s1 s2) = mkStatement r ctx s1 $$ mkStatement r ctx s2
mkStatement _ _   (SPar _ _ _)   = error "Not implemented: Boogie.mkStatement SPar" {- run in sequence, copying packet -}
mkStatement r ctx (SITE _ c t e) = (pp "if" <> (parens $ mkExpr r ctx c) <+> lbrace)
                                  $$
                                  (nest' $ mkStatement r ctx t)
                                  $$
                                  (maybe rbrace
                                         (\s -> (rbrace <+> pp "else" <+> lbrace) 
                                                $$
                                                (nest' $ mkStatement r ctx s)
                                                $$
                                                rbrace)
                                         e)
mkStatement r ctx (STest _ c)    = pp "if" <> (parens $ mkExpr r ctx (EUnOp nopos Not c)) <+> (braces $ pp "return" <> semi)
mkStatement r ctx (SSet _ l rhs) = checkBounds r ctx rhs
                                   $$
                                   mkAssign r ctx l [] rhs
mkStatement r ctx (SSend _ dst)  = let ELocation _ rname ks = dst in
                                   checkBounds r ctx dst
                                   $$
                                   checkDepth
                                   $$
                                   case M.lookup rname ?rmap of
                                        Nothing -> pp outputVar .:= (pp outputTypeName <> 
                                                                    (parens $ pp pktVar <> comma <+>
                                                                              (apply rname $ map (mkExpr r ctx) ks)))
                                        Just _  -> call (mkRoleName rname) $ map (mkExpr r ctx) $ ks ++ [EPacket nopos]
mkStatement r ctx (SSendND _ n c) = let rl' = getRole r n in
                                    checkBounds r (CtxSend ctx rl') c
                                    $$
                                    checkDepth
                                    $$
                                    case M.lookup n ?rmap of
                                         Nothing -> (havoc $ pp outputVar)
                                                    $$
                                                    assume notDropped
                                                    $$
                                                    (assume $ apply ("is#" ++ n) [apply ("loc#" ++ outputTypeName) [pp outputVar]])
                                                    $$
                                                    (assume $ checkBVBounds r (map (\k -> (mkExpr r (CtxSend ctx rl') (EDotVar nopos $ name k), fieldType k)) $ roleKeys rl'))
                                                    $$
                                                    (assume $ mkExpr r (CtxSend ctx rl') c)
                                         Just _  -> (havoc $ pp locationVar)
                                                    $$
                                                    (assume $ apply ("is#" ++ n) [pp locationVar])
                                                    $$
                                                    (let ?p = pktVar
                                                         ?mset = []
                                                         ?locals = M.empty
                                                         ?r = r
                                                         ?c = CtxSend ctx rl'
                                                         ?loc = pp locationVar in
                                                     (assume $ checkBVBounds r (map (\k -> (mkExpr' (EDotVar nopos $ name k), fieldType k)) $ roleKeys rl'))
                                                     $$
                                                     (assume $ mkExpr' c))
                                                    $$
                                                    (call (mkRoleName n) 
                                                          $ (map (\k -> apply (name k ++ "#" ++ n) [pp locationVar]) $ roleKeys rl') ++ [pp pktVar])
mkStatement r ctx (SHavoc _ e)    = havoc' r (mkExpr r ctx e, typ r ctx e)
mkStatement r ctx (SAssume _ e)   = assume $ mkExpr r ctx e
mkStatement r ctx (SLet _ _ n v)  = checkBounds r ctx v
                                    $$
                                    mkAssign r ctx (EVar nopos n) [] v
mkStatement r ctx (SFork _ vs c b) = (vcat $ map (\v -> havoc' r (pp $ name v, fieldType v)) vs)
                                     $$
                                     (assume $ mkExpr r ctx' c)
                                     $$
                                     mkStatement r ctx' b
    where ctx' = CtxFork ctx vs


checkDepth :: (?maxdepth::Int) => Doc
checkDepth = (pp depthVar .:= (pp depthVar .+ pp "1"))
             $$
             (assrt $ pp depthVar .< pp ?maxdepth)

checkBounds :: Refine -> ECtx -> Expr -> Doc
checkBounds r c e = if null es then empty else (assrt $ checkBVBounds r es)
    where es = map (\e' -> (mkExpr r c e', typ r c e')) $ filter (isUInt r c) $ arithSubExpr e
          arithSubExpr (EVar _ _)          = []
          arithSubExpr (EDotVar _ _)       = []
          arithSubExpr (EPacket _)         = []
          arithSubExpr e'@(EApply _ f as)  = let func = getFunc r f in
                                             (maybe [] (\_ -> if' (isStruct r c e' || isUInt r c e') [e'] []) $ funcDef func) ++ concatMap arithSubExpr as
          arithSubExpr (EField _ s _)      = arithSubExpr s
          arithSubExpr (ELocation _ _ as)  = concatMap arithSubExpr as
          arithSubExpr (EBool _ _)         = []
          arithSubExpr (EInt _ _ _)        = []
          arithSubExpr (EStruct _ _ fs)    = concatMap arithSubExpr fs
          arithSubExpr e'@(EBinOp _ op l x) = arithSubExpr l ++ arithSubExpr x ++ 
                                             (if elem op [Plus, Minus] then [e'] else [])
          arithSubExpr (EUnOp _ _ e')      = arithSubExpr e'
          arithSubExpr (ESlice _ e' _ _)   = arithSubExpr e'
          arithSubExpr (ECond _ cs d)      = arithSubExpr d ++ (concatMap (\(x,v) -> arithSubExpr x ++ arithSubExpr v) cs)


mkAssign :: Refine -> ECtx -> Expr -> [String] -> Expr -> Doc
mkAssign rf ctx (EField _ e f) fs r = mkAssign rf ctx e (f:fs) r
mkAssign rf ctx l fs r              = mkExpr rf ctx l .:= mkAssignRHS rf ctx l fs r

mkAssignRHS :: Refine -> ECtx -> Expr -> [String] -> Expr -> Doc
mkAssignRHS rf ctx _ []     r                = mkExpr rf ctx r
mkAssignRHS rf ctx l (f:fs) r                = apply n $ map (\fn -> if' (fn == f) (mkAssignRHS rf ctx l' fs r) (mkExpr rf ctx $ EField nopos l fn)) fns
    where l' = EField nopos l f
          fns = map name $ typeFields $ typ' rf ctx l
          n = typeName $ typ'' rf ctx l

mkAbstRoleBody :: Refine -> Role -> Doc
mkAbstRoleBody r rl = 
    (let ?r = r in
     mkAbstStatement (CtxRole rl) [] M.empty [] $ roleBody rl)
    $$
    checkDropped


mkAbstStatement :: (?r::Refine) => ECtx -> MSet -> Locals -> [Statement] -> Statement -> Doc
mkAbstStatement ctx mset locals nxt (SSeq _ s1 s2) = mkAbstStatement ctx mset locals (s2:nxt) s1
mkAbstStatement _   _    _      _   (SPar _ _ _)   = error "Not implemented: Boogie.mkAbstStatement SPar" {- run in sequence, copying packet -}
mkAbstStatement ctx mset locals nxt (SITE _ c t e) = stat
    where clone = (isNothing $ statMSet ctx t) || (statMSet ctx t /= maybe (Just []) (statMSet ctx) e)
          tbranch = if clone
                       then mkAbstStatement ctx mset locals nxt t
                       else mkAbstStatement ctx mset locals []  t
          ebranch = if clone
                       then mkAbstStatement ctx mset locals nxt $ fromJust e
                       else mkAbstStatement ctx mset locals []  $ fromJust e
          suffix = if clone 
                      then empty
                      else mkNext ctx (msetUnion mset $ fromJust $ statMSet ctx t) locals nxt
          stat = (pp "if" <> (parens $ mkAbstExpr ctx mset locals c) <+> lbrace)
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
mkAbstStatement ctx mset locals nxt (STest _ c)    = pp "if" <> (parens $ mkAbstExpr ctx mset locals (EUnOp nopos Not c)) <+> (braces $ checkDropped <+> ret)
                                                     $$
                                                     mkNext ctx mset locals nxt
mkAbstStatement ctx mset locals nxt (SSet _ l rhs) = (assrt $ isDropped .|| (parens $ mkAbstExpr ctx mset' locals l .== mkAbstExpr ctx mset locals rhs))
                                                     $$
                                                     mkNext ctx mset' locals nxt
    where mset' = msetUnion [(l, exprNext ctx l)] mset
mkAbstStatement ctx mset locals []  (SSend _ dst)  = checkNotDropped
                                                     $$
                                                     (assrt $ (apply ("loc#" ++ outputTypeName) [pp outputVar]) .== (apply rname $ map (mkAbstExpr ctx mset locals) ks))
                                                     $$
                                                     (vcat $ map (\(e,_) -> assrt $ mkAbstExpr ctx mset' locals e .== mkAbstExpr ctx mset locals e) mset')
                                                     $$
                                                     ret
    where mset' = msetComplement ctx mset
          ELocation _ rname ks = dst
mkAbstStatement ctx mset locals []  (SSendND _ rl c) = checkNotDropped
                                                       $$
                                                       (assrt $ apply ("is#" ++ rl) [apply ("loc#" ++ outputTypeName) [pp outputVar]])
                                                       $$
                                                       (assrt $ mkAbstExpr (CtxSend ctx $ getRole ?r rl) mset locals c)
                                                       $$
                                                       (vcat $ map (\(e,_) -> assrt $ mkAbstExpr ctx mset' locals e .== mkAbstExpr ctx mset locals e) mset')
                                                       $$
                                                       ret
    where mset' = msetComplement ctx mset
mkAbstStatement ctx mset locals nxt (SHavoc _ e)   = mkNext ctx (msetUnion mset [(e, exprNext ctx e)]) locals nxt
mkAbstStatement ctx mset locals nxt (SAssume _ c)  = (assrt $ isDropped .|| mkAbstExpr ctx mset locals c)
                                                     $$
                                                     mkNext ctx mset locals nxt
mkAbstStatement ctx mset locals nxt (SLet _ _ n v) = mkNext ctx mset locals' nxt
    where locals' = M.insert n (mkAbstExpr ctx mset locals v) locals
mkAbstStatement _   _    _      nxt s              = error $ "Boogie.mkAbstStatement " ++ show nxt ++ " " ++ show s

mkNext :: (?r::Refine) => ECtx -> MSet -> Locals -> [Statement] -> Doc
mkNext ctx mset locals nxt = case nxt of
                                  []     -> empty
                                  (s:ss) -> mkAbstStatement ctx mset locals ss s

statMSet :: (?r::Refine) => ECtx -> Statement -> Maybe MSet
statMSet ctx (SSeq _ l r)    = maybe Nothing (\mset -> maybe Nothing (Just . msetUnion mset) $ statMSet ctx r) $ statMSet ctx l
statMSet _   (SPar _ _ _)    = error "Boogie.statMSet SPar"
statMSet ctx (SITE _ _ t me) = maybe Nothing 
                                     (\msett -> maybe Nothing 
                                                      (\msete -> if' (msetEq msete msett) (Just msete) Nothing) 
                                                      (maybe (Just []) (statMSet ctx) me)) 
                                     (statMSet ctx t)
statMSet _   (STest _ _)     = Just []
statMSet ctx (SSet _ l _)    = Just [(l, exprNext ctx l)]
statMSet _   (SSend  _ _)    = Nothing
statMSet _   (SSendND _ _ _) = Nothing
statMSet ctx (SHavoc _ l)    = Just [(l, exprNext ctx l)]
statMSet _   (SAssume _ _)   = Just []
statMSet _   (SLet _ _ _ _)  = Just []
statMSet _   (SFork _ _ _ _) = Nothing

exprNext :: (?r::Refine) => ECtx -> Expr -> Doc
exprNext c e = mkExprP (render $ apply ("pkt#" ++ outputTypeName) [pp outputVar]) ?r c e

mkRoleFuncBody :: (?rmap::RMap, ?r::Refine) => Role -> Doc
mkRoleFuncBody rl@Role{..} = 
      ite (mkExpr ?r (CtxRole rl) roleKeyRange)
          (ite (mkAbstExpr (CtxRole rl) [] M.empty rolePktGuard)
               (mkFuncStatement (CtxRole rl) [] M.empty [] roleBody)
               (pp "false"))
          (pp "false")

mkFuncStatement :: (?r::Refine, ?rmap::RMap) => ECtx -> MSet -> Locals -> [Statement] -> Statement -> Doc
mkFuncStatement ctx mset locals nxt (SSeq _ s1 s2) = mkFuncStatement ctx mset locals (s2:nxt) s1
mkFuncStatement _   _    _      _   (SPar _ _ _)   = error "Not implemented: Boogie.mkFuncStatement SPar" {- run in sequence, copying packet -}
mkFuncStatement ctx mset locals nxt (SITE _ c t e) = ite (mkAbstExpr ctx mset locals c)
                                                         (mkFuncStatement ctx mset locals nxt t)
                                                         (maybe isDropped (mkFuncStatement ctx mset locals nxt) e)
mkFuncStatement ctx mset locals nxt (STest _ c)    = ite (mkAbstExpr ctx mset locals (EUnOp nopos Not c)) 
                                                         isDropped
                                                         (mkFuncNext ctx mset locals nxt)
mkFuncStatement ctx mset locals nxt (SSet _ l rhs) = mkFuncNext ctx mset' locals nxt
    where mset' = msetUnion [(l, mkAbstExpr ctx mset locals rhs)] mset
mkFuncStatement ctx mset locals []  (SSend _ dst)  = 
    case M.lookup rname ?rmap of
         Nothing -> pp outputVar .== (apply outputTypeName [ mkAbstExpr ctx mset locals (EPacket nopos)
                                                           , apply rname $ map (mkAbstExpr ctx mset locals) ks])
         Just _  -> apply (mkRoleName rname) $ (map (mkAbstExpr ctx mset locals) $ ks ++ [EPacket nopos]) ++ [pp outputVar]
    where ELocation _ rname ks = dst
mkFuncStatement ctx mset locals []  (SSendND _ rl c) = 
    case M.lookup rl ?rmap of
         Nothing -> notDropped 
                    $&& 
                    (apply ("is#" ++ rl) [apply ("loc#" ++ outputTypeName) [pp outputVar]])
                    $&&
                    (mkAbstExpr (CtxSend ctx $ getRole ?r rl) mset locals c)
                    $&&
                    (apply ("pkt#" ++ outputTypeName) [pp outputVar] .== mkAbstExpr ctx mset locals (EPacket nopos))
         Just _  -> error "Not implemented: Boogie::mkFuncStatement SSendND"
mkFuncStatement ctx mset locals nxt (SLet _ _ n v) = mkFuncNext ctx mset locals' nxt
    where locals' = M.insert n (mkAbstExpr ctx mset locals v) locals
mkFuncStatement ctx mset locals nxt (SHavoc _ e)   = exists [mkField $ Field nopos vname $ typ ?r ctx e] $ mkFuncNext ctx mset' locals nxt
    where vname = "_" ++ (replace "." "_" $ show e)
          mset' = msetUnion mset [(e, pp vname)]
mkFuncStatement ctx mset locals nxt (SAssume _ c)  = (mkAbstExpr ctx mset locals c) $&& (mkFuncNext ctx mset locals nxt)
mkFuncStatement ctx mset locals _   (SFork _ vs c b) = exists (map mkField vs) ((mkAbstExpr ctx' mset locals c) $&& (mkFuncStatement ctx' mset locals [] b))
    where ctx' = CtxFork ctx vs
mkFuncStatement _   _    _      nxt s              = error $ "Boogie.mkFuncStatement " ++ show nxt ++ " " ++ show s

mkFuncNext :: (?rmap::RMap, ?r::Refine) => ECtx -> MSet -> Locals -> [Statement] -> Doc
mkFuncNext ctx mset locals nxt = case nxt of
                                      []     -> empty
                                      (s:ss) -> mkFuncStatement ctx mset locals ss s

isDropped :: Doc
isDropped = apply "is#Dropped" [pp outputVar]

notDropped :: Doc
notDropped = apply "!is#Dropped" [pp outputVar]

checkDropped :: Doc
checkDropped = assrt isDropped

checkNotDropped :: Doc
checkNotDropped = assrt notDropped


msetComplement :: (?r::Refine) => ECtx -> MSet -> MSet
msetComplement ctx mset = msetComplement' (EPacket nopos)
    where msetComplement' e = if isJust $ lookup e mset
                                 then []
                                 else if (overlapsMSet ctx e mset)
                                         then let TStruct _ fs = typ' ?r ctx e in
                                              concatMap (msetComplement' . EField nopos e . name) fs
                                         else [(e, exprNext ctx e)]

mkBoundsCheckers :: Refine -> Doc
mkBoundsCheckers r = vcat $ map (\t -> case t of 
                                            TUser _ n -> mkStructChecker r n
                                            TUInt _ w -> mkBVChecker w
                                            _         -> empty)
                                $ collectTypes r

mkBVChecker :: Int -> Doc
mkBVChecker w = (pp "function" <+> (apply ("checkBounds" ++ show w) [pp "x" .: pp "int"]) .: (pp "bool") <+> lbrace)
                $$
                (nest' $ pp $ "(x >= 0) && (x < " ++ show ((2^w)::Integer) ++ ")")
                $$
                rbrace

mkStructChecker :: Refine -> String -> Doc
mkStructChecker r sname = 
    (pp "function" <+> (apply ("checkBounds" ++ sname) [pp "x" .: pp sname]) .: (pp "bool") <+> lbrace)
    $$
    (nest' cond)
    $$
    rbrace
    where TStruct _ fs = typ' r undefined $ TUser nopos sname
          cond = checkBVBounds r $ map (\(Field _ n t) -> (apply (n++"#"++sname) [pp "x"], t)) fs


collectTypes :: Refine -> [Type]
collectTypes r@Refine{..} = let ?r = r in
                            nub $ concatMap (\t -> let t'' = typ'' r undefined $ TUser nopos $ tdefName t
                                                       t' = typ' r undefined $ tdefType t in
                                                   t'' : case t' of
                                                              TStruct _ fs -> map (typ'' r undefined . fieldType) fs
                                                              _            -> []) refineTypes ++
                                  concatMap (\f -> maybe [] (exprCollectTypes (CtxFunc f)) $ funcDef f) refineFuncs ++
                                  concatMap (\a -> exprCollectTypes (CtxAssume a) $ assExpr a) refineAssumes ++
                                  concatMap (\rl -> map (typ' r (CtxRole rl)) $ roleKeys rl) refineRoles ++
                                  concatMap (\rl -> exprCollectTypes (CtxRole rl) $ roleKeyRange rl) refineRoles ++
                                  concatMap (\rl -> exprCollectTypes (CtxRole rl) $ rolePktGuard rl) refineRoles ++
                                  concatMap (\rl -> statCollectTypes (CtxRole rl) $ roleBody rl) refineRoles

statCollectTypes :: (?r::Refine) => ECtx -> Statement -> [Type]
statCollectTypes ctx (SSeq _ l r)     = statCollectTypes ctx l ++ statCollectTypes ctx r
statCollectTypes ctx (SPar  _ l r)    = statCollectTypes ctx l ++ statCollectTypes ctx r
statCollectTypes ctx (SITE _ c t me)  = exprCollectTypes ctx c ++ statCollectTypes ctx t ++ maybe [] (statCollectTypes ctx) me
statCollectTypes ctx (STest _ c)      = exprCollectTypes ctx c
statCollectTypes ctx (SSet _ l r)     = exprCollectTypes ctx l ++ exprCollectTypes ctx r
statCollectTypes ctx (SSend _ d)      = exprCollectTypes ctx d
statCollectTypes ctx (SSendND _ n c)  = exprCollectTypes (CtxSend ctx $ getRole ?r n) c
statCollectTypes _   (SHavoc _ _)     = []
statCollectTypes ctx (SAssume _ c)    = exprCollectTypes ctx c
statCollectTypes ctx (SLet _ t _ v)   = (typ' ?r ctx t) : exprCollectTypes ctx v
statCollectTypes ctx (SFork _ vs c b) = map (typ' ?r ctx) vs ++ exprCollectTypes (CtxFork ctx vs) c ++ statCollectTypes (CtxFork ctx vs) b


exprCollectTypes :: (?r::Refine) => ECtx -> Expr -> [Type]
exprCollectTypes c e = (typ' ?r c e) : exprCollectTypes' c e

exprCollectTypes' :: (?r::Refine) => ECtx -> Expr -> [Type]
exprCollectTypes' c (EApply _ _ as)    = concatMap (exprCollectTypes c) as
exprCollectTypes' c (EField _ s _)     = exprCollectTypes c s
exprCollectTypes' c (ELocation _ _ as) = concatMap (exprCollectTypes c) as
exprCollectTypes' c (EStruct _ _ fs)   = concatMap (exprCollectTypes c) fs
exprCollectTypes' c (EBinOp _ _ l r)   = exprCollectTypes c l ++ exprCollectTypes c r
exprCollectTypes' c (EUnOp _ _ e)      = exprCollectTypes c e
exprCollectTypes' c (ESlice _ e _ _)   = exprCollectTypes c e
exprCollectTypes' c (ECond _ cs d)     = concatMap (\(e, v) -> exprCollectTypes c e ++ exprCollectTypes c v) cs ++ exprCollectTypes c d
exprCollectTypes' _ _                  = []


--mkBVOps :: Refine -> Doc
--mkBVOps r = vcat $ map mkOpDecl $ collectOps r
--
--mkOpDecl :: (Either UOp BOp, Int) -> Doc
--mkOpDecl (Right Lt   , w) = mkBOpDecl "bvult" (bvbopname Lt)    w "bool" 
--mkOpDecl (Right Gt   , w) = mkBOpDecl "bvugt" (bvbopname Gt)    w "bool" 
--mkOpDecl (Right Lte  , w) = mkBOpDecl "bvule" (bvbopname Lte)   w "bool" 
--mkOpDecl (Right Gte  , w) = mkBOpDecl "bvuge" (bvbopname Gte)   w "bool" 
--mkOpDecl (Right Plus , w) = mkBOpDecl "bvadd" (bvbopname Plus)  w (bvtname w)
--mkOpDecl (Right Minus, w) = mkBOpDecl "bvsub" (bvbopname Minus) w (bvtname w)
--mkOpDecl _                = empty
--
--mkBOpDecl builtin opname w retname = pp $ "function {:bvbuiltin \"" ++ builtin ++ "\"} BV" ++ show w ++ "_" ++ opname ++ "(x:" ++ bvtname w ++ ", " ++ "y:" ++ bvtname w ++ ")" ++ " returns (" ++ retname ++ ");"
--bvtname w = "bv" ++ show w


--collectOps :: Refine -> [(Either UOp BOp, Int)]
--collectOps r@Refine{..} = let ?r = r in
--                          nub $ concatMap (\f -> maybe [] (exprCollectOps (CtxFunc f)) $ funcDef f) refineFuncs ++
--                                concatMap (\a -> exprCollectOps (CtxAssume a) $ assExpr a) refineAssumes ++
--                                concatMap (\rl -> exprCollectOps (CtxRole rl) $ roleKeyRange rl) refineRoles ++
--                                concatMap (\rl -> exprCollectOps (CtxRole rl) $ rolePktGuard rl) refineRoles ++
--                                concatMap (\rl -> statCollectOps rl $ roleBody rl) refineRoles
--
--statCollectOps :: (?r::Refine) => Role -> Statement -> [(Either UOp BOp, Int)]
--statCollectOps rl (SSeq _ l r)    = statCollectOps rl l ++ statCollectOps rl r
--statCollectOps rl (SPar  _ l r)   = statCollectOps rl l ++ statCollectOps rl r
--statCollectOps rl (SITE _ c t me) = exprCollectOps (CtxRole rl) c ++ statCollectOps rl t ++ maybe [] (statCollectOps rl) me
--statCollectOps rl (STest _ c)     = exprCollectOps (CtxRole rl) c
--statCollectOps rl (SSet _ l r)    = exprCollectOps (CtxRole rl) l ++ exprCollectOps (CtxRole rl) r
--statCollectOps rl (SSend _ d)     = exprCollectOps (CtxRole rl) d
--statCollectOps rl (SSendND _ n c) = exprCollectOps (CtxSend rl $ getRole ?r n) c
--statCollectOps _  (SHavoc _ _)    = []
--statCollectOps rl (SAssume _ c)   = exprCollectOps (CtxRole rl) c
--
--exprCollectOps :: (?r::Refine) => ECtx -> Expr -> [(Either UOp BOp, Int)]
--exprCollectOps c (EApply _ _ as)    = concatMap (exprCollectOps c) as
--exprCollectOps c (EField _ s _)     = exprCollectOps c s
--exprCollectOps c (ELocation _ _ as) = concatMap (exprCollectOps c) as
--exprCollectOps c (EStruct _ _ fs)   = concatMap (exprCollectOps c) fs
--exprCollectOps c (EBinOp _ op l r)  = (exprCollectOps c l ++ exprCollectOps c r) ++ 
--                                      case typ' ?r c l of
--                                            TUInt _ w -> [(Right op, w)]
--                                            _         -> []
--exprCollectOps c (EUnOp _ _ e)      = exprCollectOps c e
--exprCollectOps c (ECond _ cs d)     = concatMap (\(e, v) -> exprCollectOps c e ++ exprCollectOps c v) cs ++ exprCollectOps c d
--exprCollectOps _ _ = []
