module Syntax where

import Lex

type Command = WithSource Command'

data Command'
  = Assign LHS Expr
  | If [(Expr, [Command])] (Maybe [Command])
  | For (String, Expr) [Command]
  | While Expr [Command]
  | Break
  | Continue
  | Return
  | Function (LHS, String, [String]) [Command]
  | Switch Expr [(Expr, [Command])] (Maybe [Command])
  | Direct Dir
  | Respond Res
  | GeneratedCode [Command]
  deriving (Show)

type Dir = WithSource Dir'

data Dir'
  = Declare (String, TensorType)
  | Rename String String
  deriving Show

type TensorType = WithSource TensorType'

data TensorType'
  = Tensor ((String, Expr), (String, Expr)) EntryType
  deriving Show

type EntryType = WithSource EntryType'

data EntryType'
  = Ty Expr
  | Cmhn (String, Expr) Expr
  deriving (Show)

type Res = [Tok]

type Expr = WithSource Expr'

data Expr'
  = Var String
  | App Expr [Expr]
  | Brp Expr [Expr] -- brace projection, eg `e { 5, 7 }`
  | Dot Expr String -- projection from a struct
  | Mat [[Expr]]
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

data LHS'
  = LVar String
  | LApp LHS [Expr]
  | LBrp LHS [Expr]
  | LDot LHS String
  | LMat [Either Tilde LHS]
  deriving (Show)

data Tilde = Tilde deriving Show

type LHS = WithSource LHS'

pattern EmptyLHS = LMat [] :<=: (-1,[])

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
