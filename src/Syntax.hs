module Syntax where

data Command
  = Assign LHS Expr
  deriving (Show)

data Expr
  = Var String
  | IntLiteral Int
  | StringLiteral String
  | DoubleLiteral Double
  | UnaryOp UnOperator Expr
  | BinaryOp BinOperator Expr Expr
  | App String [Expr]
  | Matrix [[Expr]]
  deriving (Show)

data LHS
  = LVar String
  deriving (Show)

data UnOperator
  = UPlus
  | UMinus
  | UTilde -- logical negation
  deriving (Show)


data BinOperator
  = Plus
  | Minus
  | Times
  | And
  | Or
  -- ...
  deriving (Show)
