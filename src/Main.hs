module Main where

import System.Environment
import qualified Data.Text.IO as T

import Lex

main :: IO ()
main = do
  [file] <- getArgs
  d <- T.readFile file
  putStrLn $ show (lexer $ unix d)
