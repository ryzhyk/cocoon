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
{-# LANGUAGE ImplicitParams #-}

module Boogie.BoogieExpr ( mkExpr
                         , mkExpr'
                         , mkAbstExpr
                         , mkExprP) where

import Text.PrettyPrint
import qualified Data.Map as M
import Data.Maybe

import Boogie.BoogieHelpers
import Type
import PP
import Syntax
import Name
import Pos
import Builtins
import NS


mkExpr :: Refine -> ECtx -> Expr -> Doc
mkExpr r c e = mkExprP pktVar r c e

mkAbstExpr :: (?r::Refine) => ECtx -> MSet -> Locals -> Expr -> Doc
mkAbstExpr c mset locals e = let ?mset = mset 
                                 ?locals = locals
                                 ?c = c
                                 ?loc = apply ("loc#" ++ outputTypeName) [pp outputVar]
                                 ?p = "_pkt" in 
                              mkExpr' e

mkExprP :: String -> Refine -> ECtx -> Expr -> Doc
mkExprP p r c e = let ?c = c
                      ?p = p 
                      ?r = r 
                      ?loc = apply ("loc#" ++ outputTypeName) [pp outputVar]
                      ?mset = [] 
                      ?locals = M.empty in
                  mkExpr' e

-- Generage Boogie expression.
-- Replace packet fields in ?mset with field of outputVar
mkExpr' :: (?p::String, ?mset::MSet, ?locals::Locals, ?r::Refine, ?c::ECtx, ?loc::Doc) => Expr -> Doc
mkExpr' (EVar _ v)              = case M.lookup v ?locals of 
                                       Nothing  -> pp v
                                       Just val -> val
mkExpr' (EDotVar _ v)           = let CtxSend _ rl = ?c in 
                                  apply (v ++ "#" ++ (name rl)) [?loc]
mkExpr' e@(EPacket _)           = mkPktField e
mkExpr' (EApply _ f as)         = apply f $ map mkExpr' as
mkExpr' (EBuiltin _ f as)       = (bfuncPrintBoogie $ getBuiltin f) as
mkExpr' e@(EField _ s f) | isPktField s = mkPktField e
                         | otherwise    = 
                               let TUser _ tn = typ'' ?r ?c s
                               in pp f <> char '#' <> pp tn <> (parens $ mkExpr' s)
    where isPktField (EField _ s' _) = isPktField s'
          isPktField (EPacket _)     = True
          isPktField _               = False
mkExpr' (ELocation _ _ _)       = error "Not implemented: Boogie.mkExpr' ELocation"
mkExpr' (EBool _ True)          = pp "true"
mkExpr' (EBool _ False)         = pp "false"
mkExpr' (EInt _ _ v)            = pp v -- <> text "bv" <> pp w
mkExpr' (EStruct _ n fs)        = apply n $ map mkExpr' fs
mkExpr' (EBinOp _ Eq e1 e2)     = mkExpr' e1 .== mkExpr' e2
mkExpr' (EBinOp _ Neq e1 e2)    = mkExpr' e1 .!= mkExpr' e2
mkExpr' (EBinOp _ And e1 e2)    = mkExpr' e1 .&& mkExpr' e2
mkExpr' (EBinOp _ Or e1 e2)     = mkExpr' e1 .|| mkExpr' e2
mkExpr' (EBinOp _ Impl e1 e2)   = mkExpr' e1 .=> mkExpr' e2
mkExpr' (EBinOp _ Lt e1 e2)     = mkExpr' e1 .<  mkExpr' e2
mkExpr' (EBinOp _ Gt e1 e2)     = mkExpr' e1 .>  mkExpr' e2
mkExpr' (EBinOp _ Lte e1 e2)    = mkExpr' e1 .<= mkExpr' e2
mkExpr' (EBinOp _ Gte e1 e2)    = mkExpr' e1 .>= mkExpr' e2
mkExpr' (EBinOp _ Plus e1 e2)   = mkExpr' e1 .+  mkExpr' e2
mkExpr' (EBinOp _ Minus e1 e2)  = mkExpr' e1 .-  mkExpr' e2
mkExpr' (EBinOp _ ShiftR e1 (EInt _ _ i)) = apply "_div" [mkExpr' e1, pp $ (2^i::Integer)]
mkExpr' e@(EBinOp _ ShiftR _ _) = error $ "Not implemented Boogie.mkExpr' " ++ show e
mkExpr' (EBinOp _ ShiftL e1 (EInt _ _ i)) = apply "_mod" [mkExpr' e1 .* (pp $ (2^i::Integer)), pp $ (2^w::Integer)]
                                  where TUInt _ w = typ' ?r ?c e1
mkExpr' e@(EBinOp _ ShiftL _ _) = error $ "Not implemented Boogie.mkExpr' " ++ show e
mkExpr' (EBinOp _ Mod e1 e2)    = apply "_mod" [mkExpr' e1, mkExpr' e2]
mkExpr' (EBinOp _ Concat e1 e2) = apply "_concat" [mkExpr' e1, mkExpr' e2, pp $ (2^(w1+w2)::Integer)]
                                  where TUInt _ w1 = typ' ?r ?c e1
                                        TUInt _ w2 = typ' ?r ?c e2
mkExpr' (EUnOp _ Not e)         = parens $ char '!' <> mkExpr' e
--mkExpr' (ESlice _ e h l)        = mkExpr' e <> (brackets $ pp (h+1) <> colon <> pp l)
mkExpr' (ESlice _ e h l)        = apply "_slice" [mkExpr' e, pp h, pp l, pp $ (2^(h-l+1)::Integer)]
mkExpr' (ECond _ cs d)          = mkCond cs d 

mkPktField :: (?p::String, ?mset::MSet, ?r::Refine, ?c::ECtx) => Expr -> Doc
mkPktField e = 
    -- Parent or e in mset -- outp.field
    if isInMSet e
       then field e
       else if not (overlapsMSet ?c e ?mset)
               then -- None of the children overlaps with mset -- generate as is
                    field e
               else -- otherwise -- constructor with recursive calls for fields
                    let TUser _ tn = typ'' ?r ?c e
                        TStruct _ fs = typ' ?r ?c e in
                    (apply tn $ map (mkPktField . EField nopos e . name) fs)
    where isInMSet x = (isJust $ lookup x ?mset) ||
                       case x of
                            EField _ p _ -> isInMSet p
                            _            -> False
          field x = case lookup x ?mset of
                         Nothing -> case x of
                                         EField _ s f -> let TUser _ tn = typ'' ?r ?c s in
                                                         pp f <> char '#' <> pp tn <> (parens $ field s)
                                         EPacket _    -> pp ?p
                                         x'           -> error $ "Boogie.mkPktField.field " ++ show x'
                         Just e' -> e'

--          field (EPacket _)    = p
--          field p (EField _ s f) = let TUser _ tn = typ'' ?r ?c s
--                                   in pp f <> char '#' <> pp tn <> (parens $ field p s)
--          field _ e'             = error $ "Boogie.mkPktField.field " ++ show e'


mkCond :: (?p::String, ?mset::MSet, ?locals::Locals, ?r::Refine, ?c::ECtx, ?loc::Doc) => [(Expr,Expr)] -> Expr -> Doc
mkCond [] d             = mkExpr' d
mkCond ((cond, e):cs) d = parens $ pp "if" <> (parens $ mkExpr' cond) <+> pp "then" <+> mkExpr' e
                                                                      <+> pp "else" <+> mkCond cs d
