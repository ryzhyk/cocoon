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
{-# LANGUAGE RecordWildCards, ImplicitParams #-}

import System.Environment
import Text.Parsec.Prim
import Control.Monad
import System.FilePath.Posix
import Text.PrettyPrint
import Text.Printf
import Data.Maybe
import Data.List
import System.Directory
import System.IO.Error
import System.IO
import System.Console.GetOpt

import Parse
import Validate
import P4.P4
import Topology
import MiniNet.MiniNet
import Name
import Syntax
import NS
import Expr
import PP
import Boogie.Boogie
import Util
import qualified NetKAT.NetKAT as NK

data TOption = CCN String
             | CFG String
             | Bound String
             | DoBoogie
             | DoP4
             | DoNetKAT
        
options :: [OptDescr TOption]
options = [ Option ['i'] []             (ReqArg CCN "FILE")            "input Cocoon file"
          , Option []    ["cfg"]        (ReqArg CFG "FILE")            "Cocoon config file"
          , Option ['b'] ["bound"]      (ReqArg Bound "BOUND")         "integer bound on the number of hops"
          , Option []    ["boogie"]     (NoArg DoBoogie)               "enable Boogie backend"
          , Option []    ["p4"]         (NoArg DoP4)                   "enable P4 backend"
          , Option []    ["netkat"]     (NoArg DoNetKAT)               "enable NetKAT backend"
          ]

data Config = Config { confCCNFile      :: FilePath
                     , confCfgFile      :: Maybe FilePath
                     , confBound        :: Int
                     , confDoBoogie     :: Bool
                     , confDoP4         :: Bool
                     , confDoNetKAT     :: Bool
                     }

defaultConfig = Config { confCCNFile      = ""
                       , confCfgFile      = Nothing
                       , confBound        = 15
                       , confDoBoogie     = False
                       , confDoP4         = False
                       , confDoNetKAT     = False
                       }


addOption :: TOption -> Config -> Config
addOption (CCN f)   config = config{ confCCNFile  = f}
addOption (CFG f)   config = config{ confCfgFile  = Just f}
addOption (Bound b) config = config{ confBound    = case reads b of
                                                         []        -> error "invalid bound specified"
                                                         ((i,_):_) -> i}
addOption DoBoogie  config = config{ confDoBoogie = True}
addOption DoP4      config = config{ confDoP4     = True}
addOption DoNetKAT  config = config{ confDoNetKAT = True}

main = do
    args <- getArgs
    prog <- getProgName
    config <- case getOpt Permute options args of
                   (flags, [], []) -> return $ foldr addOption defaultConfig flags
                   _ -> fail $ usageInfo ("Usage: " ++ prog ++ " [OPTION...]") options 

    let fname  = confCCNFile config
        cfname = confCfgFile config
        (dir, file) = splitFileName fname
        (basename,_) = splitExtension file
        workdir = dir </> basename
        bound = confBound config
    createDirectoryIfMissing False workdir
    fdata <- readFile fname
    spec <- case parse cocoonGrammar fname fdata of
                 Left  e    -> fail $ "Failed to parse input file: " ++ show e
                 Right spec -> return spec
    combined <- case validate spec of
                     Left e   -> fail $ "Validation error: " ++ e
                     Right rs -> return rs
    let final = last combined
    putStrLn "Validation complete"

    let ps = pairs combined

    when (confDoBoogie config) $ do
        let boogieSpecs = (head combined, refinementToBoogie Nothing (head combined) bound) :
                          map (\(r1,r2) -> (r2, refinementToBoogie (Just r1) r2 bound)) ps
            boogiedir = workdir </> "boogie"
        createDirectoryIfMissing False boogiedir
        oldfiles <- listDirectory boogiedir
        mapM_ (removeFile . (boogiedir </>)) oldfiles
        mapIdxM_ (\(_, (asms, mroles)) i -> do -- putStrLn $ "Verifying refinement " ++ show i ++ " with " ++ (show $ length asms) ++ " verifiable assumptions , " ++ (maybe "_" (show . length) mroles) ++ " roles" 
                                               let specN = printf "spec%02d" i
                                               mapIdxM_ (\(_, b) j -> do writeFile (boogiedir </> addExtension (specN ++ "_asm" ++ show j) "bpl") (render b)) asms
                                               maybe (return ())
                                                     (mapM_ (\(rl, b) -> do writeFile (boogiedir </> addExtension (specN ++ "_" ++ rl) "bpl") (render b)))
                                                     mroles)
                 boogieSpecs
        putStrLn "Verification condition generation complete"

    topology <- case generateTopology final of
                     Left e  -> fail $ "Error generating network topology: " ++ e
                     Right t -> return t
    when (confDoP4 config) $ do
        let (mntopology, instmap) = generateMininetTopology final topology
            p4switches = genP4Switches final topology
        writeFile (workdir </> addExtension basename "mn") mntopology
        mapM_ (\(P4Switch descr p4 cmd _) -> do let swname = fromJust $ lookup descr instmap
                                                writeFile (workdir </> addExtension (addExtension basename swname) "p4")  (render p4)
                                                writeFile (workdir </> addExtension (addExtension basename swname) "txt") (render cmd)) 
              p4switches      
        -- DO NOT MODIFY this string: the run_network.py script uses it to detect the 
        -- end of the compilation phase
        putStrLn "Network generation complete"
        hFlush stdout
        maybe (return()) (refreshTables workdir basename instmap final Nothing p4switches) cfname

    when (confDoNetKAT config) $ do
        mapM_ (\f -> when (isNothing $ funcDef f) $ fail $ "Function " ++ name f ++ " is undefined") $ refineFuncs final
        let mkPhyLinks :: InstanceMap PortLinks -> InstanceMap PhyPortLinks
            mkPhyLinks (InstanceMap (Left m)) = InstanceMap $ Left $ map (mapSnd mkPhyLinks) m
            mkPhyLinks (InstanceMap (Right links)) = InstanceMap $ Right $ map (\(p,_,ports) -> (p, map(\(pnum,rport) -> (pnum, pnum, rport)) ports)) links
        let phytopo = map (mapSnd mkPhyLinks) topology
        let nkswitches = NK.genSwitches final phytopo
            policy = foldr (\(InstanceDescr _ ((EInt _ _ swid):_), pol) acc -> NK.NKITE (NK.NKTest $ NK.NKSwitch swid) pol acc) NK.nkdrop nkswitches
        writeFile (workdir </> "policy.kat") $ render $ pp policy
        putStrLn "NetKAT generation complete"

pairs :: [a] -> [(a,a)]
pairs (x:y:xs) = (x,y) : pairs (y:xs)
pairs _        = []

-- Update command files for dynamic actions modified in the new configuration.
-- workdir  - work directory where all P4 files are stored
-- basename - name of the spec to prepended to all filenames
-- base     - base specification before configuration was applied to it
-- prev     - specification with previous configuration
-- switches - switch definitions derived from base
-- cfname   - configuration file
refreshTables :: String -> String -> NodeMap -> Refine -> Maybe Refine -> [P4Switch] -> String -> IO ()
refreshTables workdir basename instmap base prev switches cfname = do
    mcombined <- 
        do cfgdata <- readFile cfname
           cfg <- case parse cfgGrammar cfname cfgdata of
                       Left  e    -> fail $ "Failed to parse config file: " ++ show e
                       Right spec -> return spec
           combined <- case validateConfig base cfg of
                            Left e   -> fail $ "Validation error: " ++ e
                            Right rs -> return rs
           let modFuncs = case prev of 
                               Nothing  -> refineFuncs combined
                               Just old -> filter (\f -> maybe True (f /= ) $ lookupFunc old (name f)) $ refineFuncs combined
               modFNames = map name modFuncs
           putStrLn $ "Functions changed: " ++ (intercalate " " $ map name modFuncs)
           let modSwitches = case prev of
                                  Nothing  -> switches
                                  Just old -> filter (any (not . null . intersect modFNames . map name . exprFuncsRec old . p4dynExpr) . p4DynActs) switches
           mapM_ (\P4Switch{..} -> do let swname = fromJust $ lookup p4Descr instmap
                                          cmds = vcat $ punctuate (pp "") $ p4Init : map (vcat . populateTable combined) p4DynActs
                                      --putStrLn $ "Switch " ++ show p4Descr ++ " " ++ swname  
                                      writeFile (workdir </> addExtension (addExtension basename swname) "txt") (render cmds))
                 modSwitches
           putStrLn $ "Switches updated: " ++ (intercalate " " $ map (\sw -> fromJust $ lookup (p4Descr sw) instmap) modSwitches)

           -- DO NOT MODIFY this string: the run_network.py script uses it to detect the 
           -- end of the compilation phase
           putStrLn "Network configuration complete"
           hFlush stdout
           return $ Just combined
        `catchIOError` 
           \e -> do putStrLn ("Exception: " ++ show e)
                    putStrLn ("Regenerating the entire configuration next time")
                    hFlush stdout
                    return Nothing
    let wait = do inp <- getLine
                  when (inp /= "update") wait
    wait
    refreshTables workdir basename instmap base mcombined switches cfname

