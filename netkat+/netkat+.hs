{-# LANGUAGE RecordWildCards, ImplicitParams #-}

import System.Environment
import Text.Parsec.Prim
import Control.Monad
import System.FilePath.Posix
import Text.PrettyPrint
import Data.Maybe
import Data.List
import System.Directory
import System.IO.Error
import System.IO

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


main = do
    args <- getArgs
    prog <- getProgName
    when (length args > 2 || length args < 1) $ fail $ "Usage: " ++ prog ++ " <spec_file> [<config_file>]"
    let fname  = head args
        cfname = if length args >= 2
                    then Just $ args !! 1
                    else Nothing
        (dir, file) = splitFileName fname
        (basename,_) = splitExtension file
        workdir = dir </> basename
    createDirectoryIfMissing False workdir
    fdata <- readFile fname
    spec <- case parse nkplusGrammar fname fdata of
                 Left  e    -> fail $ "Failed to parse input file: " ++ show e
                 Right spec -> return spec
    combined <- case validate spec of
                     Left e   -> fail $ "Validation error: " ++ e
                     Right rs -> return rs
    let final = last combined
    putStrLn "Validation successful"

    let ps = pairs combined
    let boogieSpecs = (head combined, refinementToBoogie Nothing (head combined)) :
                      map (\(r1,r2) -> (r2, refinementToBoogie (Just r1) r2)) ps
        boogiedir = workdir </> "boogie"
    createDirectoryIfMissing False boogiedir
    mapIdxM_ (\(_, (asms, mroles)) i -> do putStrLn $ "Verifying refinement " ++ show i ++ " with " ++ (show $ length asms) ++ " verifiable assumptions , " ++ (maybe "_" (show . length) mroles) ++ " roles" 
                                           mapIdxM_ (\(_, b) j -> do writeFile (boogiedir </> addExtension ("spec" ++ show i ++ "_asm" ++ show j) "bpl") (render b)) asms
                                           maybe (return ())
                                                 (mapM_ (\(rl, b) -> do writeFile (boogiedir </> addExtension ("spec" ++ show i ++ "_" ++ rl) "bpl") (render b)))
                                                 mroles)
             boogieSpecs
    
    putStrLn "Verification successful"

    topology <- case generateTopology final of
                     Left e  -> fail $ "Error generating network topology: " ++ e
                     Right t -> return t
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

