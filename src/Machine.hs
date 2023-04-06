module Machine where

import Control.Monad
import Control.Newtype
import Data.Monoid
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

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

freshNames :: [String] -> MachineState -> ([Name], MachineState)
freshNames [] st = ([], st)
freshNames (s:ss) st = case fresh s st of
   (n, st) -> case freshNames ss st of
     (ns, st) -> (n:ns, st)

data Frame
  = Source Source
  | BlockRest [Command]
  | Declaration Name DeclarationType
  | Locale LocaleType
  | Expressions [Expr]
  | MatrixRows [[Expr]]
  | RenameFrame String String
  | FunctionLeft Name LHS
  | Fork (Either Fork Fork) [Frame] Problem
  deriving Show

data Fork = Solved | FunctionName Name
  deriving (Show)


data LocaleType = ScriptLocale | FunctionLocale
  deriving (Show, Eq)

data DeclarationType
  = UserDecl
      String   -- current name
      Bool     -- have we seen it in user code?
      [String] -- renamed names (we hope of length at most 1)
      Bool     -- is it capturable?
  | LabratDecl
  deriving Show

data Problem
  = File File
  | BlockTop [Command]
  | Command Command'
  | LHS LHS'
  | Done Term
  | Expression Expr'
  | Row [Expr]
  | RenameAction String String
  | FunCalled Expr'
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

type Gripe = String

nil :: Term
nil = Atom ""

yikes :: Term -> Term
yikes t = P (Atom "yikes") t

initMachine :: File -> MachineState
initMachine f = MS
  { position = B0 :<+>: []
  , problem = File f
  , namesupply = (B0 :< ("labrat", 0), 0)
  }

findDeclaration :: DeclarationType -> Bwd Frame -> Maybe (Name, Bwd Frame)
findDeclaration LabratDecl fz = Nothing
findDeclaration (UserDecl old seen news _) fz = go fz False where
  go B0 _ = Nothing
  go (fz :< Locale ScriptLocale) True = Nothing
  go (fz :< f@(Locale FunctionLocale)) _ = fmap (:< f) <$> go fz True
  go (fz :< f@(Declaration n (UserDecl old' seen' news' capturable'))) b | old == old' =
    Just (n , fz :< Declaration n (UserDecl old' (seen || seen') (union news news') capturable'))
  go (fz :< f) b = fmap (:< f) <$> go fz b

makeDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
makeDeclaration LabratDecl ms = error "making labratdecl declaration"
makeDeclaration d@(UserDecl s seen news capturable) ms = case fresh s ms of
  (n, ms) -> case position ms of
    fz :<+>: fs -> (n, ms { position = findLocale fz (Declaration n d) :<+>: fs })
  where
    findLocale B0 fr = error "Locale disappeared!"
    findLocale (fz :< l@(Locale _)) fr = fz :< fr :< l
    findLocale (fz :< f) fr = findLocale fz fr :< f

ensureDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
ensureDeclaration s ms@(MS { position = fz :<+>: fs}) = case findDeclaration s fz of
  Nothing -> makeDeclaration s ms
  Just (n, fz) -> (n, ms { position = fz :<+>: fs})

run :: MachineState -> MachineState
run ms@(MS { position = fz :<+>: [], problem = p })
  | File (cs :<=: src) <- p = case fundecls ms B0 cs of
      (ms, fz') -> run $ ms { position = fz <> fz' :< Locale ScriptLocale :< Source src :<+>: [] , problem = BlockTop cs }
  | BlockTop ((c :<=: src):cs) <- p = run $ ms { position = fz :< BlockRest cs :< Source src :<+>: [] , problem = Command c }
  | Command (Assign (lhs :<=: src) e) <- p = run $ ms { position = fz :< Expressions [e] :< Source src :<+>: [] , problem = LHS lhs }
  | LHS (LVar x) <- p = case ensureDeclaration (UserDecl x True [] True) ms of
      (n, ms) -> move $ ms { problem = Done (FreeVar n) }
  | LHS (LMat []) <- p = move $ ms { problem = Done (Atom "") }
  | Expression (Var x) <- p = case findDeclaration (UserDecl x True [] False) fz of
      Nothing -> move $ ms { problem = Done (yikes (P (Atom "OutOfScope") (Atom x))) }
      Just (n, fz)  -> move $ ms { position = fz :<+>: [], problem = Done (FreeVar n) }
  | Expression (App (f :<=: src) args) <- p = run $ ms { position = fz :< Expressions args :< Source src :<+>: [], problem = FunCalled f }
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
  | FunCalled f <- p = run $ ms { problem = Expression f }
--  | Expression (Lambda xs t) <- p = _
  | Row rs <- p = case rs of
      [] -> move $ ms { problem = Done nil }
      ((r :<=: src):rs) -> run $ ms { position = fz :< Expressions rs :< Source src :<+>: [], problem = Expression r }

  | Command (Direct (Rename old new :<=: src)) <- p = run $ ms { position = fz :< Source src :<+>: [] , problem = RenameAction old new }
  | RenameAction old new <- p = case ensureDeclaration (UserDecl old False [new] True) ms of
      (n, ms) -> move $ ms { problem = Done nil}

  | Command (Function (lhs, fname, args) cs) <- p = case findDeclaration (UserDecl fname True [] False) fz of
      Nothing -> error "function should have been declared already"
      Just (fname, fz) -> case freshNames args ms of
        (names, ms) -> let decls = map (\(n, s) -> Declaration n (UserDecl s True [] False)) (zip names args) in
          case fundecls ms B0 cs of
            (ms, fz') -> move $ ms { position = (fz <> fz') <>< decls :< Locale FunctionLocale :< FunctionLeft fname lhs :< BlockRest cs :<+>: []
                                   , problem = Done nil }

-- run ms = trace ("Falling through. Problem = " ++ show (problem ms)) $ move ms
run ms = move ms

-- if move sees a Left fork, it should switch to Right and run
-- if move sees a Right fork, switch to Left and keep moving
move :: MachineState -> MachineState
move ms@(MS { position = fz :< fr :<+>: fs, problem = Done t })
  | Fork (Right frk) fs' p' <- fr = move $ ms{ position = fz :<+>: Fork (Left frk) fs (Done t) : fs', problem = p'}
  | BlockRest cs <- fr = case cs of
      [] -> move $ ms { position = fz :< Fork (Right Solved) fs (Done t) :<+>: [], problem = Done nil }
      ((c :<=: src):cs) -> run $ ms { position = fz :< Fork (Right Solved) fs (Done t) :< BlockRest cs :< Source src :<+>: [], problem = Command c }
--  | AssignLeft (e :<=: src) <- fr = run $ ms { position = fz :< Solved fs t :< Source src :<+>: [], problem = Expression e }
  | Expressions as <- fr = case as of
      [] -> move $ ms { position = fz :< Fork (Right Solved) fs (Done t) :<+>: [], problem = Done nil }
      ((e :<=: src):as) -> run $ ms { position = fz :< Fork (Right Solved) fs (Done t) :< Expressions as :< Source src :<+>: [], problem = Expression e }
  | MatrixRows rs <- fr = case rs of
      [] -> move $ ms { position = fz :< Fork (Right Solved) fs (Done t) :<+>: [], problem = Done nil }
      (r:rs) -> run $ ms { position = fz :< Fork (Right Solved) fs (Done t) :< MatrixRows rs :<+>: [], problem = Row r }
  | FunctionLeft fname (lhs :<=: src) <- fr = run $
    ms { position = fz :< Fork (Right $ FunctionName fname) fs (Done t) :< Source src :<+>: [], problem = LHS lhs }
move ms@(MS { position = fz :< fr :<+>: fs, problem = Done t }) = move $ ms { position = fz :<+>: fr : fs }
move ms = ms

fundecls :: MachineState -> Bwd Frame -> [Command] -> (MachineState, Bwd Frame)
fundecls ms fz [] = (ms, fz)
fundecls ms fz (Function (_, fname, _) _ :<=: src:cs) = case fresh fname ms of
  (n, ms) -> fundecls ms (fz :< Declaration n (UserDecl fname False [] False)) cs
fundecls ms fz (c:cs) = fundecls ms fz cs
