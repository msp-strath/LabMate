module Main where

import System.Environment
import System.Console.Terminal.Size (size, width)

import qualified Data.Text.IO as T

import Lex
import Lisp

main :: IO ()
main = do
  [file] <- getArgs
  d <- T.readFile file
  let l = tokenStreamToLisp (lexer $ unix d)
  termSize <- size
  let w = maybe 80 width termSize
  putStrLn $ pretty w l
