module Parse.Matlab where

import Control.Monad
import Control.Applicative

import Bwd
import Hide
import Lex

import Syntax
import Parse

pcommand :: Parser Command
pcommand = Assign <$> plhs <* punc "=" <*> pexpr 0

plhs :: Parser LHS
plhs = LVar <$> pnom

pexpr :: Int -> Parser Expr
pexpr i =
      Var <$> pnom
  <|> IntLiteral <$> pint
  <|> StringLiteral <$> pstringlit
  <|> DoubleLiteral <$> pdouble
  <|> BinaryOp Operator <$> undefined
  <|> App <$> undefined
  <|> Matrix <$> undefined

pint :: Parser Int
pint = undefined

pdouble :: Parser Double
pdouble = undefined

pstringlit :: Parser String
pstringlit = undefined
