module Main where

import System.Environment
import System.Console.Terminal.Size (size, width)
import System.Directory
import System.FilePath

import qualified Data.Text.IO as T

import Data.Map (Map)
import qualified Data.Map as Map

import Bwd

import Lex
import Lisp

import Syntax

import Parse
import Parse.Matlab
import Machine

main :: IO ()
main = do
  getArgs >>= \case
    [] -> actDir "."
    [f] -> do
      doesDirectoryExist f >>= \case
        True -> actDir f
        False -> actFile f >>= \case
          Right (tab, cs@(_ :<=: (n,src))) -> do
            seeToks src
            print n
            putStrLn "---------"
            let out = (run (initMachine cs))
            print out
            putStrLn "---------"
            putStrLn $ reassemble (n,tab) out
          Left e -> printError e
    x -> putStrLn $ "Unrecognised arguments: " ++ (show x)

printError :: (FilePath, Reach, Int) -> IO ()
printError (f, r, n) = do putStr (f ++ ": parse error "); print r; putStr (show n) ; putStrLn " parses\n"

actFile :: FilePath -> IO (Either (FilePath, Reach, Int) (Map Nonce String, WithSource [Command]))
actFile f = do
  doesFileExist f >>= \case
    False -> error $ "File does not exist: " ++ f
    True -> do
      d <- T.readFile f
      let l = lexer $ unix d
      -- termSize <- size
      -- let w = maybe 80 width termSize
      -- putStrLn $ pretty w l
      case parser pfile (Map.empty, 0) l of
        (_, [(_,cs,(tab,_),_)]) -> do
          pure (Right (tab, cs))
        (r, xs) -> pure (Left (f, r, length xs))
          -- putStrLn $ pretty w (tokenStreamToLisp l)

actDir :: FilePath -> IO ()
actDir f = do
  files <- filter (isExtensionOf ".m") <$> listDirectory f
  done <- traverse actFile ((f </>) <$> files)
  let nothings = length [ () | Right _ <- done ]
  let total = length done
  let msg = "Parsed " ++ show nothings ++ "/" ++ show total ++ " files.\n"
  traverse printError [ x | Left x <- done ]
  putStr msg

