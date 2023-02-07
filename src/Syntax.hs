module Syntax where

data Command
  = Assign LHS Expr
  deriving (Show)

data Expr
  = Var String
  | IntLiteral Int
  | StringLiteral String
  | DoubleLiteral Double
  | BinaryOp Operator Expr Expr
  | App String [Expr]
  | Matrix [[Expr]]
  deriving (Show)

data LHS
  = LVar String
  deriving (Show)

data Operator
  = Plus
  | Minus
  | Times
  | And
  | Or
  -- ...
  deriving (Show)
