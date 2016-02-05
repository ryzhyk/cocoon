import System.Environment
import Text.Parsec.Prim
import Control.Monad

import Parse
import Validate
import P4

main = do
    args <- getArgs
    prog <- getProgName
    when (length args /= 1) $ fail $ "Usage: " ++ prog ++ " <file>"
    let fname = head args
    fdata <- readFile fname
    spec <- case parse nkplusGrammar fname fdata of
                 Left  e    -> fail $ "Failed to parse input file: " ++ show e
                 Right spec -> return spec
    case validate spec of
         Left e  -> fail $ "Validation error: " ++ e
         Right _ -> return ()
    putStrLn "Validation successful"
