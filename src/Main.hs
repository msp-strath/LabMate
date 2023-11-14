module Main where

import System.Environment
import System.Console.Terminal.Size (size, width)
import System.Directory
import System.FilePath
import System.IO
import System.Exit

import qualified Data.Text.IO as T
import Data.Text (Text)

import Data.Bifunctor (first)
import Data.Foldable (traverse_)
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monad (unless)
import Control.Monad.State

import Options.Applicative hiding (ParseError)

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
import Term

data Conf = Conf
  { src :: String
  , hideVersion :: Bool
  , verbose :: Bool
  }

pconf = info
  (Conf <$> argument str (value "-" <> help "Matlab source file")
        <*> switch (long "no-version"
                    <> help "Surpress printing out labmate version in the output")
        <*> switch (long "verbose"
                    <> help "Print out the machine state after execution")
  <**> helper)
  (fullDesc <> progDesc "Labmate - an interactive assistent for Matlab")

main :: IO ()
main = do
  conf@Conf{src} <- execParser pconf
  case src of
    "-" -> stdin >>= go conf
    f -> do
      doesDirectoryExist f >>= \case
        True  -> actDir f
        False -> actFile f >>= go conf
 where
   stdin = T.getContents >>= actInput
   go Conf{hideVersion, verbose} (Right (tab, cs@(_ :<=: (n, src)))) = do
      let out = execState run (initMachine cs tab)
      when verbose $
        traverse_ putStrLn (pprint out rootNamespace)
      unless hideVersion $
        putStrLn ("%< LabMate " ++ showVersion version)
      putStrLn $ reassemble n out
   go _ (Left e) = do printError e; exitWith fatalExitCode


type ParseError = (Maybe FilePath, Reach, Int)
type ParsedFile = (Map Nonce String, WithSource [Command])

printError :: ParseError -> IO ()
printError (f, r, n) = do
 putError msg; putError (show r); putError (show n); putError " parses\n"
  where
    msg = foldMap (++ ": ") f ++ "parser error "
    putError = hPutStr stderr

actInput :: Text -> IO (Either ParseError ParsedFile)
actInput c = do
  let l = lexer $ unix c
  -- termSize <- size
  -- let w = maybe 80 width termSize
  -- putStrLn $ pretty w l
  case parser pfile (Map.empty, 0) l of
    (_, [(_,cs,(tab,_),_)]) -> do
      track ("Nonces = " ++ show tab ++ "\n Commands = " ++ show cs) $
        pure (Right (tab, cs))
    (r, xs) -> pure (Left (Nothing, r, length xs))
    -- putStrLn $ pretty w (tokenStreamToLisp l)

actFile :: FilePath -> IO (Either ParseError ParsedFile)
actFile f = doesFileExist f >>= \case
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
  traverse_ printError [ x | Left x <- done ]
  putStr msg

fatalExitCode :: ExitCode
fatalExitCode = ExitFailure 10

couldBeBetterExitCode :: ExitCode
couldBeBetterExitCode = ExitFailure 1
