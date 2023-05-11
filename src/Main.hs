module Main where

import System.Environment
import System.Console.Terminal.Size (size, width)
import System.Directory
import System.FilePath
import System.IO
import System.Exit

import qualified Data.Text.IO as T
import Data.Text (Text)

import Data.Map (Map)
import qualified Data.Map as Map

import Data.Bifunctor (first)

import Bwd

import Lex
import Lisp

import Syntax

import Parse
import Parse.Matlab
import Machine
import Machine.Reassemble

import Data.Version
import Paths_LabRat

type ParseError = (Maybe FilePath, Reach, Int)

main :: IO ()
main = do
  getArgs >>= \case
    [] -> stdin >>= go
    ["-"] -> stdin >>= go
    [f] -> do
      doesDirectoryExist f >>= \case
        True -> actDir f
        False -> actFile f >>= go
    x -> putStrLn $ "Unrecognised arguments: " ++ show x
 where
   stdin = T.getContents >>= actInput
   go (Right (tab, cs@(_ :<=: (n,src)))) = do
      let out = run (initMachine cs tab)
      putStrLn ("%< LabRat " ++ showVersion version)
      putStrLn $ reassemble n out
   go (Left e) = do printError e; exitFailure

printError :: ParseError -> IO ()
printError (f, r, n) = do
 putError msg; putError (show r); putError (show n); putError " parses\n"
  where
    msg = foldMap (++ ": ") f ++ "parser error "
    putError = hPutStr stderr

actInput :: Text -> IO (Either ParseError (Map Nonce String, WithSource [Command]))
actInput c = do
  let l = lexer $ unix c
  -- termSize <- size
  -- let w = maybe 80 width termSize
  -- putStrLn $ pretty w l
  case parser pfile (Map.empty, 0) l of
    (_, [(_,cs,(tab,_),_)]) -> do
      pure (Right (tab, cs))
    (r, xs) -> pure (Left (Nothing, r, length xs))
    -- putStrLn $ pretty w (tokenStreamToLisp l)

actFile :: FilePath -> IO (Either ParseError (Map Nonce String, WithSource [Command]))
actFile f = do
  doesFileExist f >>= \case
    False -> error $ "File does not exist: " ++ f
    True -> fmap (first (\(_, r, p) -> (Just f, r, p))) $ T.readFile f >>= actInput

actDir :: FilePath -> IO ()
actDir f = do
  files <- filter (isExtensionOf ".m") <$> listDirectory f
  done <- traverse actFile ((f </>) <$> files)
  let nothings = length [ () | Right _ <- done ]
  let total = length done
  let msg = "Parsed " ++ show nothings ++ "/" ++ show total ++ " files.\n"
  traverse printError [ x | Left x <- done ]
  putStr msg
