{-
Copyrights (c) 2017. VMware, Inc. All right reserved. 
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

-- Convert Cocoon spec to OpenFlow with Necera extensions

module OpenFlow.OpenFlow where

data Mask = Mask Int Integer

-- TODO: add format field (IP4, IP6, MAC, etc)
data Value = Value { valWidth :: Int
                   , valVal   :: Integer}
                   deriving (Eq)

data Field = Field { fieldName :: String
                   , fieldWidth :: Int}

data Match = Match { matchField :: Field
                   , matchMask  :: Maybe Mask
                   , matchVal   :: Value
                   }

data Expr = EField Field (Maybe (Int, Int))
          | EVal   Value


exprIsConst :: Expr -> Bool
exprIsConst (EVal _) = True
exprIsConst _        = False

type HTable  = Int
type Prio    = Int
type GroupId = Int

data Action = ActionOutput {actPort :: Expr}
            | ActionGroup  {actGroup :: GroupId}
            | ActionDrop
            | ActionSet    {actLHS :: Expr, actRHS :: Expr}
            | ActionGoto   {actGotoTable :: HTable}

data Flow = Flow { flowPriority :: Prio
                 , flowMatch    :: [Match]
                 , flowActions  :: [Action]
                 }

data GroupType = GroupAll
               | GroupIndirect

type BucketId = Int
data Bucket = Bucket (Maybe BucketId) [Action]

data Group = Group GroupId GroupType [Bucket]

data Command = AddFlow   HTable Flow
             | DelFlow   HTable Prio [Match]
             | AddGroup  Group
             | DelGroup  GroupId
             | AddBucket GroupId Bucket
             | DelBucket GroupId BucketId

{-data Table = Table { oftFlows   :: [Flow]
                   , oftDefault :: [Action]
                   }

data Switch = Switch { ofTables :: [Table]
                         }


type PMap = [((String, String), IM.IntMap Int)]

-- Generator state
data State = State { ofsTables       :: [Table]
                       , ofsNextRegister :: Int
                       , ofsRegisterMap  :: [(Expr, (Register, Maybe (Int, Int)))]
                       }

-- Allocate register for a local variable
allocRegister32 :: State State Register
allocRegister32 = undefined

allocRegister64 :: State State Register
allocRegister64 = undefined

-- e must be a scalar expression
allocRegisterFor :: (?r::Refine, ?c::ECtx) => Expr -> State State (Register, Maybe (Int, Int))
allocRegisterFor e = do
    if w <= 32
       then liftM (, Just (0, w - 1)) allocRegister32
       else if w <= 64
               then liftM (, Just (0, w - 1)) allocRegister64
               else error $ "Cannot allocate OpenFlow register for expression " ++ show e
    where w = scalarExprWidth e

freeRegister :: Register -> State State ()
freeRegister = undefined

setRegister :: Expr -> Register -> Maybe (Int, Int) -> State State ()
setRegister e r slice = modify (\s -> s{ofsRegisterMap = (e, (r, slice)) : (ofsRegisterMap s)})

lookupRegister :: Expr -> State State (Register, Maybe (Int, Int))
lookupRegister = undefined

scalarExprWidth :: (?r::Refine, ?c::ECtx) => Expr -> Int
scalarExprWidth e = case typ' ?r ?c e of
                         TBool _   -> 1
                         TUInt _ b -> b
                         _         -> error $ "OpenFlow.scalarExprWidth " ++ show e

addTable :: Table -> State State HTable
addTable t = do
    h <- gets $ length . ofsTables
    modify (\s -> s{ofsTables = (ofsTables s) ++ [t]})
    return h

-- Generate all switches in the topology
genSwitches :: Refine -> PhyTopology -> [Switch]
genSwitches r topology = 
    concatMap (\(switch, imap) -> map (\(descr, links) -> let kmap = M.fromList $ zip (map name $ roleKeys $ getRole r $ name switch) $ idescKeys descr
                                                              pmap = concatMap (\((i,o),plinks) -> let m = IM.fromList $ map (\(l,p,_) -> (l,p)) plinks
                                                                                                   in [((i,o), m)]) links
                                                          in mkSwitch r kmap pmap) $ instMapFlatten switch imap) 
              $ filter ((== NodeSwitch) . nodeType . fst) topology


-- Generate  switch 
mkSwitch :: Refine -> KMap -> PMap -> Switch
mkSwitch r kmap pmap = 
    let ?r = r in
    let ?pmap = pmap in
    let ?kmap = kmap in
    Switch $ ofsTables $ execState mkSwitch' (State [] 0 [])

mkSwitch' :: (?r::Refine, ?kmap::KMap, ?pmap::PMap) => State State ()
mkSwitch' = do
    regInPort <- allocRegister32
    mapM_ ((\pname -> let role = getRole ?r pname 
                          pvar = EVar nopos $ name $ last $ roleKeys role in
                      setRegister pvar regInPort $ Just (0, scalarExprWidth pvar - 1)) . fst . fst) ?pmap
    hSend <- mapM (mkOutputPortMap regInPort . snd) ?pmap
    hPortHandlers <- mapM (mkPortHandler regInPort hSend . fst . fst) ?pmap
    hInput <- mkInputPortMap regInPort hPortHandlers
    return ()

-- Input table: map input port number into logical Cocoon port number 
mkInputPortMap :: (?pmap :: PMap) => Register -> [HTable] -> State State HTable
mkInputPortMap reg next = do
    let flows = concatMap (mapIdx (\(lport, pport) i -> Flow Nothing
                                                             [Match InPort Nothing $ ValInt 32 $ fromIntegral pport] 
                                                             [ ActionSet (LHS (Register reg) Nothing) (RHSConst $ ValInt 32 $ fromIntegral lport)
                                                             , ActionGoto $ next !! i]) 
                          . IM.toList . snd) ?pmap
    addTable $ Table flows [ActionDrop]

mkOutputPortMap :: Register -> IM.IntMap Int -> State State HTable
mkOutputPortMap reg m = do
    let flows = map (\(lport, pport) -> Flow Nothing
                                             [Match (Register reg) Nothing $ ValInt 32 $ fromIntegral lport] 
                                             [ActionOutput (RHSConst $ ValInt 32 $ fromIntegral pport)]) 
                    $ IM.toList m
    addTable $ Table flows [ActionDrop]

mkPortHandler :: (?r::Refine, ?kmap::KMap, ?pmap::PMap) => Register -> [HTable] -> String -> State State HTable
mkPortHandler regOutPort hSend pname = do
    hDrop <- addTable $ Table [] [ActionDrop]
    let ?hSend = hSend
        ?role = getRole ?r pname 
        ?regOutPort = regOutPort
    let ?c = CtxRole ?role
    mkStatement hDrop $ roleBody ?role

mkStatement :: (?r::Refine, ?kmap::KMap, ?pmap::PMap, ?role::Role, ?c::ECtx, ?hSend::[HTable], ?regOutPort::Register) => HTable -> Statement -> State State HTable
mkStatement next (SSeq    _ l r)    = do next' <- mkStatement next r
                                         mkStatement next' l
mkStatement _    (SPar    _ _ _)    = error "Not implemented: OpenFlow.mkStatement: SPar"
mkStatement next (SITE    _ c t me) = do hthen <- mkStatement next t
                                         helse <- maybe (return next) (mkStatement next) me
                                         mkCond c hthen (Just helse)
mkStatement next (STest   _ c)      = mkCond c next Nothing
mkStatement next (SSet    _ l r)    = do let r' = evalExpr ?kmap r
                                             lscalars = exprScalars ?r ?c l
                                             rscalars = concatMap (exprScalars ?r ?c) $ exprDeps r'
                                             twophase = not $ null $ intersect lscalars rscalars
                                         if twophase
                                            then do regs <- mapM allocRegisterFor lscalars
                                                    phase2 <- mkCopyTable next
                                                              $ map (\((reg,slice), e) -> (RHSVar (Register reg) slice, lexprToLHS e))
                                                              $ zip regs lscalars
                                                    phase1 <- mkStore phase2 r' $ map (\((reg,slice), e) -> LHS (Register reg) slice)
                                                                                $ zip regs lscalars
                                                    mapM_ (freeRegister . fst) regs
                                                    return phase1
                                            else mkStore next r' $ map lexprToLHS lscalars
mkStatement _    (SSend   _ dst)    = do let ELocation _ n ks = evalExpr ?kmap dst
                                             portIdx = fromJust $ findIndex ((== n) . snd . fst) ?pmap
                                         mkStore (?hSend !! portIdx) (last ks) [LHS (Register ?regOutPort) $ Just (0, scalarExprWidth (last ks) - 1)]
mkStatement _    (SSendND _ _ _)    = error "OpenFlow.mkStatement SSendND"
mkStatement _    (SHavoc  _ _)      = error "OpenFlow.mkStatement SHavoc" 
mkStatement _    (SAssume _ _)      = error "OpenFlow.mkStatement SAssume"
mkStatement next (SLet    _ _ n v)  = do let v' = evalExpr ?kmap v
                                             scalars = exprScalars ?r ?c $ EVar nopos n
                                         regs <- mapM (\e -> do reg <- allocRegisterFor e
                                                                setRegister e reg
                                                                return reg) scalars
                                         mkStore next v' $ map (\((r,slice), e) -> LHS (Register r) slice) $ zip regs scalars
mkStatement next (SFork   _ vs c b) = undefined


mkCond :: Expr -> HTable -> Maybe HTable -> State State HTable
mkCond = undefined

mkStore (?r::Refine, ?role::Role, ?c::ECtx) :: HTable -> Expr -> [LHS] -> State State HTable
mkStore next e dst = do
    hmain <- mkEmptyTable
    (h, _, acts) <- exprToRHS hmain e (Just dst)
    setTable hmain $ Table [] (acts ++ [ActionGoto next])
    return h

-- Compute an expression and optionally place the result to a provided location
-- next - next table in the chain
-- e    - expression to be computed
-- mlhs - location where the result of expression is to be stores, if allocated by the caller
--        if no location is provided, then one will be allocated if needed and returned by the function
-- returns: 
--      - handle to the table that performs the computation or next if no additional tables were generated
--      - location where the result of the computation can be found
--      - possibly empty list of actions to be performed in order to place it there
exprToRHS :: HTable -> Expr -> Maybe [LHS] -> State State (HTable, [RHS], [Action])
exprToRHS h e mlhs = exprToRHS' h (simplifyCond e) mlhs

exprToRHS' :: HTable -> Expr -> Maybe [LHS] -> State State (HTable, [RHS], [Action])
exprToRHS' next e@(ECond _ cs d) | condNeeds1Table e = 
exprToRHS' next (ECond _ [] d) mlhs = exprToRHS next d mlhs
exprToRHS' next (ECond _ ((c,e):cs) d) mlhs = do
    lhs <- case mlhs of
                Just lhs' -> return lhs'
                Nothing   -> mapM (liftM (\(r,slice) -> LHS (Register r) slice) . allocRegisterFor) 
                                  $ exprScalars ?r ?c e
    (hThen, rhs, []) <- exprToRHS next e (Just lhs)
    (hElse, _, [])   <- exprToRHS next (ECond nopos cs d) (Just lhs)
    hCond <- mkCond c 
                    -- for each case;
                        -- mkCond
                        -- call exprToRHS for each branch
exprToRHS' next (EBool _ v) mlhs = 
    return $ maybe (next, [rhs], []) 
                   (\lhs -> (next, maybe [lhs2rhs lhs], [ActionSet lhs rhs])
                   mlhs
    where rhs = RHSConst $ ValInt 1 (if' v 1 0)

exprToRHS' next (EInt _ w v) mlhs = 
    return $ maybe (next, [rhs], []) 
                   (\lhs -> (next, maybe [lhs2rhs lhs], [ActionSet lhs rhs])
                   mlhs
    where rhs = RHSConst $ ValInt w v

exprToRHS' next e mlhs | exprIsPacketField e = 
    return $ maybe (next, rhs, [])
             (\lhs -> (next, map lhs2rhs lhs, map (uncurry ActionSet) $ zip lhs rhs))
             mlhs
    where rhs = map mkHeaderField $ exprScalars ?r ?c e

exprToRHS' next e mlhs | exprIsVarField e = do
    rhs <- mapM mkVarField $ exprScalars ?r ?c e
    return $ maybe (next, rhs, [])
             (\lhs -> (next, map lhs2rhs lhs, map (uncurry ActionSet) $ zip lhs rhs))
             mlhs

exprToRHS' next e mlhs | exprIsFuncField e = do 
    hPlaceholder <- mkEmptyTable
    -- Compute arguments; record their locations
    (hArgs, rhss) <- foldM (\(next', rhss') a -> do (next'', rhs', []) <- exprToRHS next' a Nothing
                                                    return (next'', rhss' ++ [rhs'])) 
                           (hPlaceholder,[]) $ args e
    -- create placeholder table
    rhs <- mkPlaceholder hPlaceholder next rhss e
    freeRegisters rhss
    return (hArgs, rhs)

                 | exprIsBuiltinField e = 
                    -- Compute arguments; record their locations
                    -- Invoke builtin method to construct RHS

                 | otherwise = error $ "OpenFlow.exprToRHS: unexpected expression " ++ show e



lexprToLHS :: Expr -> LHS
lexprToLHS = undefined

mkCopyTable :: HTable -> [(RHS, LHS)] -> State State HTable
mkCopyTable = undefined

mkHeaderField :: Expr -> LHS
mkHeaderField = undefined

mkVarField :: Expr -> State State LHS
mkVarField = undefined {-(liftM ((\(reg, slice) -> RHSVar (Register reg) slice) . fromJust) . lookupRegister)-}

-- SFork: use the first conjunct to generate multicast group.  Use the rest as filters.
-- -}
