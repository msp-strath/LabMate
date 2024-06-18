module Syntax where

import Lex
import Hide

type Command = WithSource Command'

type File = WithSource [Command]

data Command'
  = Assign LHS Expr
  | If [(Expr, [Command])] (Maybe [Command])
  | For (WithSource String, Expr) [Command]
  | While Expr [Command]
  | Break
  | Continue
  | Return
  -- should function names / args be enclosed in WithSource?
  | Function (LHS, WithSource String, [WithSource String]) [Command]
  | Switch Expr [(Expr, [Command])] (Maybe [Command])
  | Direct ResponseLocation Dir
  | Respond Res
  | GeneratedCode [Command]
  deriving (Show)


type ResponseLocation = (Nonce, Int)
type Dir = WithSource Dir'
type Dir' = (WithSource DirHeader, Maybe DirBody)

data DirHeader
  = Declare [WithSource String] ConcreteType
  | Rename String String
  | InputFormat String {- name of function -}
  | Typecheck ConcreteType Expr
  | SynthType Expr
  | Dimensions
      (WithSource String) -- name of the Abelian group
      (WithSource String) -- name of the quantity semiring
      [WithSource String] -- the set of generators (quoted)
  | Unit
      (WithSource String)
      TypeExpr
--  | EverythingOkay
  deriving Show

data DirBody
  = InputFormatBody [String]
 deriving Show

type TensorType = WithSource TensorType'
type TypeExpr = WithSource TypeExpr'

data TensorType'
  = Tensor ((String, TypeExpr), (String, TypeExpr)) TypeExpr
  deriving Show

data VOrH = Vertical | Horizontal
  deriving Show

-- possibly incomplete list of type level expressions
data TypeExpr'
  = TyVar String -- might also be constants, e.g. Double
  | TyNum Int
  | TyAtom String
  | TyApp TypeExpr [TypeExpr]
  -- | TyMat [[TypeExpr]]
  | TyJux VOrH TypeExpr TypeExpr
  | TyNil VOrH
  | TyBinaryOp BinOperator TypeExpr TypeExpr
  | TyUnaryOp UnOperator TypeExpr
  | TyStringLiteral String
  | TyBraces (Maybe TypeExpr)
  deriving Show

tyMat :: [[TypeExpr]] -> TypeExpr'
tyMat exps = what $ go Vertical (go Horizontal id) exps
  where
    jux _ e (TyNil _ :<=: _) = e
    jux dir e e' = noSource $ TyJux dir e e'

    nil dir = noSource $ TyNil dir

    go :: VOrH -> (a -> TypeExpr) -> [a] -> TypeExpr
    go dir pre = foldr (jux dir . pre) (nil dir)

type Res = [Tok]

type ConcreteType = TensorType

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

toTypeExpr' :: Expr' -> Maybe TypeExpr'
toTypeExpr' (Var x) = pure $ TyVar x
toTypeExpr' (IntLiteral n) = pure $ TyNum n
toTypeExpr' (StringLiteral s) = pure $ TyStringLiteral s
toTypeExpr' (BinaryOp op x y) = TyBinaryOp op <$> toTypeExpr x <*> toTypeExpr y
toTypeExpr' (Mat exps) = do
   exps <- traverse (traverse toTypeExpr) exps
   pure $ tyMat exps
-- FIXME : add more
toTypeExpr' _ = Nothing

toTypeExpr :: Expr -> Maybe TypeExpr
toTypeExpr = traverse toTypeExpr'

data LHS'
  = LVar String
  | LApp LHS [Expr]
  | LBrp LHS [Expr]
  | LDot LHS String
  | LMat [Either Tilde LHS]
  deriving (Show)

data Tilde = Tilde deriving Show

type LHS = WithSource LHS'

pattern EmptyLHS = LMat [] :<=: (-1, Hide [])

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
