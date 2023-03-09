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
  | AssignLeft Expr
  | Declaration Name (Maybe String)
  | Locale
  deriving Show

data Problem
  = File File
  | BlockTop [Command]
  | Command Command'
  | LHS LHS'
  deriving Show

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
  | Command (Assign (lhs :<=: src) e) <- p = run $ ms { position = fz :< AssignLeft e :< Source src :<+>: [] , problem = LHS lhs }
  | LHS (LVar x) <- p = case ensureDeclaration x ms of
      (n, ms) -> _
run ms = ms
