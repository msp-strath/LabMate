module Main where

import System.Environment
import qualified Data.Text.IO as T

import Lex
import Lisp

main :: IO ()
main = do
  [file] <- getArgs
  d <- T.readFile file
  let l = tokenStreamToLisp (lexer $ unix d)
  putStrLn $ pretty 79 l
