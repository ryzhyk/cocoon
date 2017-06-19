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
{-# LANGUAGE RecordWildCards, ImplicitParams, LambdaCase #-}

import System.Environment
import Text.Parsec.Prim
import Text.PrettyPrint
import System.FilePath.Posix
import System.Directory
import System.Console.GetOpt
import Control.Exception
import Control.Monad

import qualified Datalog.Dataflog as DL
import Parse
import Validate
import SQL
import Controller
import CLI
import Syntax

data TOption = CCN String
             | Action String
             | Bound String
             | DoBoogie
             | Do1Refinement
             | DoP4
             | DoNetKAT
             | Port String
        
data CCNAction = ActionSQL 
               | ActionDL
               | ActionController
               | ActionCLI
               | ActionNone
               deriving Eq

options :: [OptDescr TOption]
options = [ Option ['i'] []             (ReqArg CCN "FILE")            "input Cocoon file"
          , Option []    ["action"]     (ReqArg Action "ACTION")       "action: one of sql, dl, controller, cli"
          , Option ['b'] ["bound"]      (ReqArg Bound "BOUND")         "integer bound on the number of hops"
          , Option []    ["boogie"]     (NoArg DoBoogie)               "enable Boogie backend"
          , Option []    ["1refinement"](NoArg Do1Refinement)          "generate Boogie encoding of one big refinement"
          , Option []    ["p4"]         (NoArg DoP4)                   "enable P4 backend"
          , Option []    ["netkat"]     (NoArg DoNetKAT)               "enable NetKAT backend"
          , Option []    ["port"]       (ReqArg Port "PORT_NUMBER")    "cocoon controller port number, default: 5000"
          ]

data Config = Config { confCCNFile      :: FilePath
                     , confAction       :: CCNAction
                     , confBound        :: Int
                     , confDoBoogie     :: Bool
                     , confDo1Refinement:: Bool
                     , confDoP4         :: Bool
                     , confDoNetKAT     :: Bool
                     , confCtlPort      :: Int
                     }

defaultConfig = Config { confCCNFile      = ""
                       , confAction       = ActionNone
                       , confBound        = 15
                       , confDoBoogie     = False
                       , confDo1Refinement= False
                       , confDoP4         = False
                       , confDoNetKAT     = False
                       , confCtlPort      = 5000
                       }


addOption :: Config -> TOption -> IO Config
addOption config (CCN f)        = return config{ confCCNFile  = f}
addOption config (Action a)     = do a' <- case a of
                                                "sql"        -> return ActionSQL
                                                "controller" -> return ActionController
                                                "cli"        -> return ActionCLI
                                                "dl"         -> return ActionDL
                                                _            -> error "invalid action"
                                     return config{confAction = a'}
addOption config (Bound b)      = do b' <- case reads b of
                                                []        -> error "invalid bound specified"
                                                ((i,_):_) -> return i
                                     return config{confBound = b'}
addOption config DoBoogie       = return config{ confDoBoogie      = True}
addOption config Do1Refinement  = return config{ confDo1Refinement = True}
addOption config DoP4           = return config{ confDoP4          = True}
addOption config DoNetKAT       = return config{ confDoNetKAT      = True}
addOption config (Port p)       = do p' <- case reads p of 
                                                []        -> error "invalid port number"
                                                ((i,_):_) -> return i
                                     return config{confCtlPort = p'}

validateConfig :: Config -> IO ()
validateConfig Config{..} = do
    when (confAction == ActionNone)
         $ error "action not specified"
    when ((confAction /= ActionCLI) && (confCCNFile == ""))
         $ error "input file not specified"

main = do
    args <- getArgs
    prog <- getProgName
    config <- case getOpt Permute options args of
                   (flags, [], []) -> do conf <- foldM addOption defaultConfig flags
                                         validateConfig conf
                                         return conf
                                      `catch`
                                      (\e -> do putStrLn $ usageInfo ("Usage: " ++ prog ++ " [OPTION...]") options
                                                throw (e::SomeException))
                   _ -> error $ usageInfo ("Usage: " ++ prog ++ " [OPTION...]") options 
 
    let fname  = confCCNFile config
        (dir, file) = splitFileName fname
        (basename,_) = splitExtension file
        workdir = dir </> basename
    case confAction config of
         ActionCLI -> controllerCLI (confCtlPort config)
         ActionSQL -> do 
             combined <- readValidate fname workdir
             let schema = mkSchema basename combined
                 schfile = workdir </> addExtension basename "schema"
             writeFile schfile $ render schema
             putStrLn $ "Schema written to file " ++ schfile
         ActionDL -> do
             combined <- readValidate fname workdir
             --let rust = mkRust 
             --    rsfile = workdir </> addExtension basename "rs"
             --writeFile rsfile $ render rust
             --putStrLn $ "Datalog program written to file " ++ rsfile
             return ()
         ActionController -> do 
             combined <- readValidate fname workdir
             putStrLn "Starting controller"
             let logfile = workdir </> addExtension basename "log"
             controllerStart basename logfile (confCtlPort config) combined
             controllerCLI (confCtlPort config)
         ActionNone -> error "action not specified"
 
readValidate :: FilePath -> FilePath -> IO Refine
readValidate fname workdir = do
    createDirectoryIfMissing False workdir
    fdata <- readFile fname
    spec <- case parse cocoonGrammar fname fdata of
                 Left  e    -> error $ "Failed to parse input file: " ++ show e
                 Right spec -> return spec
    combined <- case validate spec of
                     Left e   -> error $ "Validation error: " ++ e
                     Right rs -> return rs
--    --mapM_ (putStrLn . ("\n" ++)  . render . pp) combined 
    putStrLn "Validation complete"
    return $ head combined 
--
--    let ps = pairs combined
--
--    when (confDoBoogie config) $ do
--        let refinedRoles = intersect (map name $ refineRoles $ head combined) (nub $ concatMap refineTarget combined)
--        let oneBigRefine = (last $ filter (not . null . refineTarget) combined){refineTarget = refinedRoles}
--            (_, oneBigRefineBoogie) = refinementToBoogie (Just $ head combined) oneBigRefine bound
--        let boogieSpecs = (head combined, refinementToBoogie Nothing (head combined) bound) :
--                          map (\(r1,r2) -> (r2, refinementToBoogie (Just r1) r2 bound)) ps
--            boogiedir = workdir </> "boogie"
--        createDirectoryIfMissing False boogiedir
--        oldfiles <- listDirectory boogiedir
--        mapM_ (removeFile . (boogiedir </>)) oldfiles
--        let writeRefine nm mroles = maybe (return ())
--                                          (mapM_ (\(rl, b) -> do writeFile (boogiedir </> addExtension (nm ++ "_" ++ rl) "bpl") (render b)))
--                                          mroles
--        mapIdxM_ (\(_, (asms, mroles)) i -> do -- putStrLn $ "Verifying refinement " ++ show i ++ " with " ++ (show $ length asms) ++ " verifiable assumptions , " ++ (maybe "_" (show . length) mroles) ++ " roles" 
--                                               let specN = printf "spec%02d" i
--                                               mapIdxM_ (\(_, b) j -> do writeFile (boogiedir </> addExtension (specN ++ "_asm" ++ show j) "bpl") (render b)) asms
--                                               writeRefine specN mroles)
--                 boogieSpecs
--        when (length combined > 1 && confDo1Refinement config) $ do
--            writeRefine "_spec" oneBigRefineBoogie
--        putStrLn "Verification condition generation complete"
--
--    topology <- case generateTopology final of
--                     Left e  -> fail $ "Error generating network topology: " ++ e
--                     Right t -> return t
--    when (confDoP4 config) $ do
--        let (mntopology, instmap) = generateMininetTopology final topology
--            p4switches = genP4Switches final topology
--        writeFile (workdir </> addExtension basename "mn") mntopology
--        mapM_ (\(P4Switch descr p4 cmd _) -> do let swname = fromJust $ lookup descr instmap
--                                                writeFile (workdir </> addExtension (addExtension basename swname) "p4")  (render p4)
--                                                writeFile (workdir </> addExtension (addExtension basename swname) "txt") (render cmd)) 
--              p4switches      
--        -- DO NOT MODIFY this string: the run_network.py script uses it to detect the 
--        -- end of the compilation phase
--        putStrLn "Network generation complete"
--        hFlush stdout
--        maybe (return()) (refreshTables workdir basename instmap final Nothing p4switches) cfname
--
--    when (confDoNetKAT config) $ do
--        mapM_ (\f -> when (isNothing $ funcDef f) $ fail $ "Function " ++ name f ++ " is undefined") $ refineFuncs final
--        let mkPhyLinks :: InstanceMap PortLinks -> InstanceMap PhyPortLinks
--            mkPhyLinks (InstanceMap (Left m)) = InstanceMap $ Left $ map (mapSnd mkPhyLinks) m
--            mkPhyLinks (InstanceMap (Right links)) = InstanceMap $ Right $ map (\(p,_,ports) -> (p, map(\(pnum,rport) -> (pnum, pnum, rport)) ports)) links
--        let phytopo = map (mapSnd mkPhyLinks) topology
--        let nkswitches = NK.genSwitches final phytopo
--            policy = foldr (\(InstanceDescr _ ((EInt _ _ swid):_), pol) acc -> NK.NKITE (NK.NKTest $ NK.NKSwitch swid) pol acc) NK.nkdrop nkswitches
--        writeFile (workdir </> "policy.kat") $ render $ pp policy
--        putStrLn "NetKAT generation complete"
--
--pairs :: [a] -> [(a,a)]
--pairs (x:y:xs) = (x,y) : pairs (y:xs)
--pairs _        = []
--
---- Update command files for dynamic actions modified in the new configuration.
---- workdir  - work directory where all P4 files are stored
---- basename - name of the spec to prepended to all filenames
---- base     - base specification before configuration was applied to it
---- prev     - specification with previous configuration
---- switches - switch definitions derived from base
---- cfname   - configuration file
--refreshTables :: String -> String -> NodeMap -> Refine -> Maybe Refine -> [P4Switch] -> String -> IO ()
--refreshTables workdir basename instmap base prev switches cfname = do
--    mcombined <- 
--        do cfgdata <- readFile cfname
--           cfg <- case parse cfgGrammar cfname cfgdata of
--                       Left  e    -> fail $ "Failed to parse config file: " ++ show e
--                       Right spec -> return spec
--           combined <- case validateConfig base cfg of
--                            Left e   -> fail $ "Validation error: " ++ e
--                            Right rs -> return rs
--           let modFuncs = case prev of 
--                               Nothing  -> refineFuncs combined
--                               Just old -> filter (\f -> maybe True (f /= ) $ lookupFunc old (name f)) $ refineFuncs combined
--               modFNames = map name modFuncs
--           putStrLn $ "Functions changed: " ++ (intercalate " " $ map name modFuncs)
--           let modSwitches = case prev of
--                                  Nothing  -> switches
--                                  Just old -> filter (any (not . null . intersect modFNames . map name . exprFuncsRec old . p4dynExpr) . p4DynActs) switches
--           mapM_ (\P4Switch{..} -> do let swname = fromJust $ lookup p4Descr instmap
--                                          cmds = vcat $ punctuate (pp "") $ p4Init : map (vcat . populateTable combined) p4DynActs
--                                      --putStrLn $ "Switch " ++ show p4Descr ++ " " ++ swname  
--                                      writeFile (workdir </> addExtension (addExtension basename swname) "txt") (render cmds))
--                 modSwitches
--           putStrLn $ "Switches updated: " ++ (intercalate " " $ map (\sw -> fromJust $ lookup (p4Descr sw) instmap) modSwitches)
--
--           -- DO NOT MODIFY this string: the run_network.py script uses it to detect the 
--           -- end of the compilation phase
--           putStrLn "Network configuration complete"
--           hFlush stdout
--           return $ Just combined
--        `catchIOError` 
--           \e -> do putStrLn ("Exception: " ++ show e)
--                    putStrLn ("Regenerating the entire configuration next time")
--                    hFlush stdout
--                    return Nothing
--    let wait = do inp <- getLine
--                  when (inp /= "update") wait
--    wait
--    refreshTables workdir basename instmap base mcombined switches cfname
--
