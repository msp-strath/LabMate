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
import Control.Monad (unless)
import Data.List

import Bwd

import Lex
import Lisp

import Syntax

import Parse
import Parse.Matlab
import Machine
import Machine.Reassemble

import Data.Version
import Paths_LabMate

type ParseError = (Maybe FilePath, Reach, Int)

main :: IO ()
main = do
  getArgs >>= noVersionEh >>= \(hideVersion, args) ->
    case args of
    [] -> stdin >>= go hideVersion
    ["-"] -> stdin >>= go hideVersion
    [f] -> do
      doesDirectoryExist f >>= \case
        True -> actDir f
        False -> actFile f >>= go hideVersion
    x -> do
      putStrLn $ "Unrecognised arguments: " ++ show x
      exitWith fatalExitCode
 where
   stdin = T.getContents >>= actInput
   go hideVersion (Right (tab, cs@(_ :<=: (n,src)))) = do
      let out = run (initMachine cs tab)
      print out
      unless hideVersion $
        putStrLn ("%< LabMate " ++ showVersion version)
      putStrLn $ reassemble n out
   go _ (Left e) = do printError e; exitWith fatalExitCode
   noVersionEh args = pure $ first (not . null) . partition (== "--no-version") $ args

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
actFile f =
  doesFileExist f >>= \case
    False -> do
      putStrLn $ "File does not exist: " ++ f
      exitWith fatalExitCode
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

fatalExitCode :: ExitCode
fatalExitCode = ExitFailure 10

couldBeBetterExitCode :: ExitCode
couldBeBetterExitCode = ExitFailure 1
