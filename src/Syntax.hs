module Syntax where

import Lex

data Command
  = Assign LHS Expr
  | If [(Expr, [Command])] (Maybe [Command])
  | For (String, Expr) [Command]
  | While Expr [Command]
  | Break
  | Continue
  | Return
  | Function (LHS, String, [String]) [Command]
  | Switch Expr [(Expr, [Command])] (Maybe [Command])
--  | ConfusedBy [Tok]
  | Direct Dir
  | Respond Res
  | GeneratedCode [Command]
  deriving (Show)

data Dir =
  Declare (String, TensorType)
  deriving Show

data TensorType
  = Tensor ((String, Expr), (String, Expr)) EntryType
  deriving Show

data EntryType
  = Ty Expr
  | Cmhn (String, Expr) Expr
  deriving (Show)

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
  | Handle String
  | Lambda [String] Expr
  deriving (Show)

data LHS' matrix
  = Var String
  | App (LHS' matrix) [Expr]
  | Brp (LHS' matrix) [Expr]
  | Dot (LHS' matrix) String
  | Mat matrix
  deriving (Show)

data Tilde = Tilde deriving Show
newtype LHS = LHS {lhs :: LHS' [Either Tilde LHS]} deriving (Show)

data UnOperator
  = UPlus
  | UMinus
  | UTilde -- logical negation
  | UTranspose
  | UDotTranspose
  deriving (Show)


data BinOperator
  = Pow Bool{-dotted?-}
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
