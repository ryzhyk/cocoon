{-# LANGUAGE ImplicitParams, RecordWildCards #-}

module Boogie.Boogie (refinementToBoogie) where

import Text.PrettyPrint
import Text.Heredoc
import qualified Data.Map as M

import Syntax

-- Prepended to generated Boogie files
headerDecls :: String
headerDecls = [str|
|type finite WithValidity t;
|]

refinementToBoogie :: Maybe Refine -> Refine -> ([(String, Doc)], [(String, Doc)])
refinementToBoogie mabst conc = (assums, roles)
    where assums = mapMaybe (\assm -> fmap (assm,) $ assumeToBoogie1 mabst conc assm) $ refineAssumes conc
          roles  = fmap (\abst -> map (\role -> (role, refinementToBoogie1 abst conc role)) $ refineTarget conc)
                        mabst

-- Generate verification condition to validate  an assumption.
-- Returns Nothing if not all functions involved in the assumption are defined
-- or if all of them were already defined in abst (in which case the 
-- assumption must have been validated during previous refinements).
assumeToBoogie1 :: Maybe Refine -> Refine -> Assume -> Maybe Doc

type RMap = M.Map String String

refinementToBoogie :: Refine -> Refine -> String -> Doc
refinementToBoogie abst conc rname = vcat $ punctuate "" [types, funcs, aroles, croles, assums, check]
    where tgts   = refineTarget conc
          armap  = M.fromList $ map (\n -> (n, "a_" ++ n) tgts
          crmap  = M.fromList $ map (\n -> (n, "c_" ++ n) tgts
          types  = vcat $ map (mkTypeDef conc) $ refineTypes conc
          funcs  = vcat $ map (mkFunc conc) $ refineFuncs conc
          aroles = let ?rmap = armap 
                       ?ovar = "abs" in 
                   vcat $ punctuate "" $ map (mkRole abst) $ refineRoles abst
          croles = let ?rmap = crmap 
                       ?ovar = "conc" in 
                   vcat $ punctuate "" $ map (mkRole conc) $ refineRoles conc
          assums = vcat $ map (mkAssume conc) $ refineAssumes conc
          check  = mkCheck abst conc rname 

mkRoleName :: (?rmap::RMap) => String -> Doc
mkRoleName n = case M.lookup n ?rmap of
                    Nothing -> pp n
                    Just n' -> pp n'

mkTypeDef :: Refine -> TypeDef -> Doc
mkTypeDef r TypeDef{..} = 
   case tdefType of
        TStruct   _ fs        -> (pp "type" <+> pp "finite" <+> char '_' <> tdefName (hsep $ map (pp . name) fs) <> semi)
                                 $$
                                 (pp "type" <+> pp tdefName <+> char '=' <+> char '_' <> tdefName <> (hsep $ map (mkType . fieldType) fs) <> semi)
        TOption   _ t         -> pp "type" <+> pp tdefName <+> char '=' <+> pp "WithValidity" <+> mkType t <> semi
        _                     -> pp "type" <+> pp tdefName <+> char '=' <+> mkType tdefType <> semi
        
mkType :: Type -> Doc 
mkType (TLocation _) = error "Not implemented: Boogie.mkType TLocation"
mkType (TBool _)     = pp "bool"
mkType (TUInt _ w)   = pp "bv" <> pp w
mkType (TUser _ n)   = pp n
mkType t             = error $ "Boogie.mkType " ++ show t

mkFunction :: Refine -> Function -> Doc
mkFunction r f@Function{..} = maybe (decl <> semi) 
                                    (\e -> decl <+> lbrace $$ nest' (mkExpr r e) $$ rbrace) 
                                    funcDef
    where decl  = pp "function" <+> (pp $ name f) 
              <>  (parens $ hsep $ punctuate comma $ map (\a -> (pp $ name a) <> colon <+> (mkType $ fieldType a)) funcArgs)
              <+> pp "returns" <> (parens $ mkType funcType)

mkRole :: (?ovar::String, ?rmap::RMap) => Refine -> Role -> Doc
mkRole r Role{..} = (pp "procedure" <+> mkRoleName roleName <+> (parens $ hsep $ punctuate comma args))
                    $$
                    (pp "requires" <+> mkExpr r roleKeyRange <> semi)
                    $$
                    (pp "modifies" <+> ?ovar <> semi <> lbrace)
                    $$
                    (nest' $ mkStatement r roleBody)
                    $$
                    rbrace
    where args = (map (\k -> (pp $ name k) <> colon <+> (mkType $ fieldType k)) roleKeys)
                 ++
                 [Field nopos pktVar $ tdefType $ getType r packetTypeName]
