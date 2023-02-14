module Syntax where

import Lex

data Command
  = Assign LHS Expr
  | If [(Expr, [Command])] (Maybe [Command])
  | For (String, Expr) [Command]
  | While Expr [Command]
  | Break
  | Continue
  | Function (LHS, String, [String]) [Command]
  | Skip
  | ConfusedBy [Tok]
  | Direct Dir
  | Respond Res
  | GeneratedCode [Command]
  deriving (Show)

data Dir = D [Tok]
  deriving Show

type Res = [Tok]

data Expr
  = EL (LHS' [[Expr]])
  | Cell [[Expr]]
  | IntLiteral Int
  | StringLiteral String
  | DoubleLiteral Double
  | UnaryOp UnOperator Expr
  | BinaryOp BinOperator Expr Expr
  | ColonAlone
  deriving (Show)

data LHS' matrix
  = Var String
  | App (LHS' matrix) [Expr]
  | Brp (LHS' matrix) [Expr]
  | Dot (LHS' matrix) String
  | Mat matrix
  deriving (Show)

newtype LHS = LHS {lhs :: LHS' [LHS]} deriving (Show)

data UnOperator
  = UPlus
  | UMinus
  | UTilde -- logical negation
  deriving (Show)


data BinOperator
  = Sup Bool{-dotted?-} Super
  | Mul Bool{-dotted?-} MulDiv
  | Plus | Minus
  | Colon
  | Comp Bool{-truly?-} Ordering
    -- <  is Comp True  LT
    -- <= is Comp False GT
    -- == is Comp True  EQ
    -- ~= is Comp False EQ
    -- >  is Comp True  GT
    -- >= is Comp False LT
  | And Bool{-strict?-} -- && is And False; & is And True
  | Or Bool{-trict?-}   -- likewise
  deriving (Show)

data MulDiv
  = Times | RDiv | LDiv
  deriving (Show)

data Super
  = Xpose | Power
  deriving (Show)
  
