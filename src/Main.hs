module Main where

import System.Environment
import System.Console.Terminal.Size (size, width)
import System.Directory
import System.FilePath

import qualified Data.Text.IO as T

import Lex
import Lisp
import Parse
import Parse.Matlab

main :: IO ()
main = do
  getArgs >>= \case
    [] -> actDir "."
    [f] -> do
      doesDirectoryExist f >>= \case
        True -> actDir f
        False -> actFile f >>= \case
          Nothing -> return ()
          Just e -> printError e
    x -> putStrLn $ "Unrecognised arguments: " ++ (show x)

printError :: (FilePath, Reach, Int) -> IO ()
printError (f, r, n) = do putStr (f ++ ": parse error "); print r; putStr (show n) ; putStrLn " parses\n"

actFile :: FilePath -> IO (Maybe (FilePath, Reach, Int))
actFile f = do
  doesFileExist f >>= \case
    False -> error $ "File does not exist: " ++ f
    True -> do
      d <- T.readFile f
      let l = lexer $ unix d
      -- termSize <- size
      -- let w = maybe 80 width termSize
      -- putStrLn $ pretty w l
      case parser pfile l of
        (_, [(_,cs,_)]) -> pure Nothing
        (r, xs) -> pure (Just (f, r, length xs))
          -- putStrLn $ pretty w (tokenStreamToLisp l)

actDir :: FilePath -> IO ()
actDir f = do
  files <- filter (isExtensionOf ".m") <$> listDirectory f
  done <- traverse actFile ((f </>) <$> files)
  let nothings = length [ () | Nothing <- done ]
  let total = length done
  let msg = "Parsed " ++ show nothings ++ "/" ++ show total ++ " files.\n"
  traverse printError [ x | Just x <- done ]
  putStr msg

