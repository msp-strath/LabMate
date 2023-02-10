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
  = Sup Bool{-dotted-} Super
  | Mul Bool{-dotted?-} MulDiv
  | Plus | Minus
  | Colon
  | Comp Bool Ordering-- e.g. <= is Comp False GT
  | And Bool{-strict?-} -- && is And False; & is And True
  | Or Bool{-trict?-}   -- likewise
  deriving (Show)

data MulDiv
  = Times | RDiv | LDiv
  deriving (Show)

data Super
  = Xpose | Power
  deriving (Show)
  