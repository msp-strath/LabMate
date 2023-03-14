module Machine where

import Control.Newtype
import Data.Monoid

import Bwd

import Lex
import Parse
import Parse.Matlab
import Syntax

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , namesupply :: (Root, Int)
  } deriving Show

type Root = Bwd (String, Int)
type Name = [(String, Int)]

name :: (Root, Int) -> String -> Name
name (r, n) s = r <>> [(s, n)]

fresh :: String -> MachineState -> (Name, MachineState)
fresh s ms = let (r, n) = namesupply ms in (name (r, n) s, ms { namesupply = (r, n+1) })

data Frame
  = Source Source
  | BlockRest [Command]
  | Declaration Name (Maybe String)
  | Locale
  | Solved [Frame] Term
  | Expressions [Expr]
  | MatrixRows [[Expr]]
  deriving Show

data Problem
  = File File
  | BlockTop [Command]
  | Command Command'
  | LHS LHS'
  | Done Term
  | Expression Expr'
  | Row [Expr]
  deriving Show

data Term
  = FreeVar Name
  | Atom String
  | P Term Term
  | Lit Lit
  deriving Show

data Lit
  = IntLit Int
  | DoubleLit Double
  | StringLit String
  deriving Show
nil :: Term
nil = Atom ""

yikes :: Term -> Term
yikes t = P (Atom "yikes") t

initMachine :: File -> MachineState
initMachine f = MS
  { position = B0 :< Locale :<+>: []
  , problem = File f
  , namesupply = (B0 :< ("labrat", 0), 0)
  }

findDeclaration :: String -> Bwd Frame -> Maybe Name
findDeclaration s = ala' Last foldMap $ \case
  Declaration n (Just s') | s == s' -> Just n
  _ -> Nothing

makeDeclaration :: String -> MachineState -> (Name, MachineState)
makeDeclaration s ms = case fresh s ms of
  (n, ms) -> case position ms of
    fz :<+>: fs -> (n, ms { position = findLocale fz (Declaration n (Just s)) :<+>: fs })
  where
    findLocale B0 fr = error "Locale disappeared!"
    findLocale (fz :< Locale) fr = fz :< fr :< Locale
    findLocale (fz :< f) fr = findLocale fz fr :< f

ensureDeclaration :: String -> MachineState -> (Name, MachineState)
ensureDeclaration s ms@(MS { position = fz :<+>: fs}) = case findDeclaration s fz of
  Nothing -> makeDeclaration s ms
  Just n -> (n, ms)

run :: MachineState -> MachineState
run ms@(MS { position = fz :<+>: [], problem = p })
  | File (cs :<=: src) <- p = run $ ms { position = fz :< Source src :<+>: [] , problem = BlockTop cs }
  | BlockTop ((c :<=: src):cs) <- p = run $ ms { position = fz :< BlockRest cs :< Source src :<+>: [] , problem = Command c }
  | Command (Assign (lhs :<=: src) e) <- p = run $ ms { position = fz :< Expressions [e] :< Source src :<+>: [] , problem = LHS lhs }
  | LHS (LVar x) <- p = case ensureDeclaration x ms of
      (n, ms) -> move $ ms { problem = Done (FreeVar n) }
  | Expression (Var x) <- p = case findDeclaration x fz of
      Nothing -> move $ ms { problem = Done (yikes (P (Atom "OutOfScope") (Atom x))) }
      Just n  -> move $ ms { problem = Done (FreeVar n) }
  | Expression (App (f :<=: src) args) <- p = run $ ms { position = fz :< Expressions args :< Source src :<+>: [], problem = Expression f }
  | Expression (Brp (e :<=: src) args) <- p = run $ ms { position = fz :< Expressions args :< Source src :<+>: [], problem = Expression e }
  | Expression (Dot (e :<=: src) fld) <- p = run $ ms { position = fz :< Source src :<+>: [], problem = Expression e }
  | Expression (Mat es) <- p = case es of
      [] -> move $ ms { problem = Done nil }
      (r:rs) -> run $ ms { position = fz :< MatrixRows rs :<+>: [], problem = Row r }
  | Expression (Cell es) <- p = case es of
      [] -> move $ ms { problem = Done nil }
      (r:rs) -> run $ ms { position = fz :< MatrixRows rs :<+>: [], problem = Row r }
  | Expression (IntLiteral i) <- p = move $ ms { problem = Done (Lit (IntLit i)) }
  | Expression (DoubleLiteral d) <- p = move $ ms { problem = Done (Lit (DoubleLit d)) }
  | Expression (StringLiteral s) <- p = move $ ms { problem = Done (Lit (StringLit s)) }
  | Expression (UnaryOp op (e :<=: src)) <- p = run $ ms { position = fz :< Source src :<+>: [], problem = Expression e }
  | Expression (BinaryOp op (e0 :<=: src0) e1) <- p = run $ ms { position = fz :< Expressions [e1] :< Source src0 :<+>: [], problem = Expression e0 }
  | Expression ColonAlone <- p = move $ ms { problem = Done (Atom ":") }
  | Expression (Handle f) <- p = move $ ms { problem = Done (P (Atom "handle") (Atom f)) }
--  | Expression (Lambda xs t) <- p = _
  | Row rs <- p = case rs of
      [] -> move $ ms { problem = Done nil }
      ((r :<=: src):rs) -> run $ ms { position = fz :< Expressions rs :< Source src :<+>: [], problem = Expression r }
run ms = move ms

move :: MachineState -> MachineState
move ms@(MS { position = fz :< fr :<+>: fs, problem = Done t })
  | BlockRest cs <- fr = case cs of
      [] -> move $ ms { position = fz :< Solved fs t :<+>: [], problem = Done nil }
      ((c :<=: src):cs) -> run $ ms { position = fz :< Solved fs t :< BlockRest cs :< Source src :<+>: [], problem = Command c }
--  | AssignLeft (e :<=: src) <- fr = run $ ms { position = fz :< Solved fs t :< Source src :<+>: [], problem = Expression e }
  | Expressions as <- fr = case as of
      [] -> move $ ms { position = fz :< Solved fs t :<+>: [], problem = Done nil }
      ((e :<=: src):as) -> run $ ms { position = fz :< Solved fs t :< Expressions as :< Source src :<+>: [], problem = Expression e }
  | MatrixRows rs <- fr = case rs of
      [] -> move $ ms { position = fz :< Solved fs t :<+>: [], problem = Done nil }
      (r:rs) -> run $ ms { position = fz :< Solved fs t :< MatrixRows rs :<+>: [], problem = Row r }

move ms@(MS { position = fz :< fr :<+>: fs, problem = Done t }) = move $ ms { position = fz :<+>: fr : fs }
move ms = ms
