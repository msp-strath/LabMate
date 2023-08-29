module Machine where

import Control.Monad
import Control.Newtype
import Data.Monoid
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

-- mgen
import TranslateContext
import Translate

import Bwd

import Lex
import Parse
import Parse.Matlab
import Syntax
import Hide
import Term
import MagicStrings

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , nameSupply :: (Root, Int)
  , nonceTable :: Map Nonce String
  } deriving Show

fresh :: String -> MachineState -> (Name, MachineState)
fresh s ms = let (r, n) = nameSupply ms in (name (r, n) s, ms { nameSupply = (r, n+1) })

freshNames :: [String] -> MachineState -> ([Name], MachineState)
freshNames [] st = ([], st)
freshNames (s:ss) st = case fresh s st of
   (n, st) -> case freshNames ss st of
     (ns, st) -> (n:ns, st)

type TERM = Term Chk ^ Z
type TYPE = Type ^ Z

data Frame where
  Source :: Source -> Frame
  BlockRest :: [Command] -> Frame
  Declaration :: Name -> TYPE -> DeclarationType -> Frame
  Definition :: NATTY n => Name -> Context n -> Maybe (Term Chk ^ n) -> Type ^ n -> Frame
  Locale :: LocaleType -> Frame
  Expressions :: [Expr] -> Frame
  TargetLHS :: LHS -> Frame
  Conditionals :: [(Expr, [Command])] -> Frame
  MatrixRows :: [[Expr]] -> Frame
  RenameFrame :: String -> String -> Frame
  FunctionLeft :: Name -> LHS -> Frame
  FormalParams :: [WithSource String] -> Frame
  Fork :: (Either Fork Fork) -> [Frame] -> Problem -> Frame

deriving instance Show Frame

data Fork = Solved | FunctionName Name
  deriving Show

data LocaleType = ScriptLocale | FunctionLocale
  deriving (Show, Eq)

data DeclarationType
  = UserDecl
      String   -- current name
      Bool     -- have we seen it in user code?
      [(String, ResponseLocation)] -- requested name and how to reply
                                   -- (we hope of length at most 1)
      Bool     -- is it capturable?
  | LabmateDecl
  deriving Show

data Problem
  = File File
  | BlockTop [Command]
  | Command Command'
  | LHS LHS'
  | FormalParam String
  | Done TERM
  | Expression Expr'
  | Row [Expr]
  | RenameAction String String ResponseLocation
  | InputFormatAction String [String] ResponseLocation
  | FunCalled Expr'
  deriving Show

data Lit
  = IntLit Int
  | DoubleLit Double
  | StringLit String
  deriving Show

data Gripe =
  RenameFail Nonce String
  deriving Show

yikes :: TERM  -> TERM
yikes t = T $^ atom "yikes" <&> t

initMachine :: File -> Map Nonce String -> MachineState
initMachine f t = MS
  { position = B0 :<+>: []
  , problem = File f
  , nameSupply = (B0 :< ("labmate", 0), 0)
  , nonceTable = t
  }

findDeclaration :: DeclarationType -> Bwd Frame -> Maybe (Name, Bwd Frame)
findDeclaration LabmateDecl fz = Nothing
findDeclaration (UserDecl old seen news _) fz = go fz False where
  go B0 _ = Nothing
  go (fz :< Locale ScriptLocale) True = Nothing
  go (fz :< f@(Locale FunctionLocale)) _ = fmap (:< f) <$> go fz True
  go (fz :< f@(Declaration n ty (UserDecl old' seen' news' capturable'))) b | old == old' =
    Just (n , fz :< Declaration n ty (UserDecl old' (seen' || seen) (news' ++ news) capturable'))
  go (fz :< f) b = fmap (:< f) <$> go fz b

makeDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
makeDeclaration LabmateDecl ms = error "making labmatedecl declaration"
makeDeclaration d@(UserDecl s seen news capturable) ms = case freshNames [s ++ "Type", s] ms of
  ([ty, n], ms) -> case position ms of
    fz :<+>: fs ->
      let frz = B0 :< Definition ty (Zy, VN) Nothing (atom SType) :< Declaration n (FreeVar ty) d
      in (n, ms { position = findLocale fz frz :<+>: fs })
  where
    findLocale B0 frz = error "Locale disappeared!"
    findLocale (fz :< l@(Locale _)) frz = (fz <> frz) :< l
    findLocale (fz :< f) frz = findLocale fz frz :< f

ensureDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
ensureDeclaration s ms@(MS { position = fz :<+>: fs}) = case findDeclaration s fz of
  Nothing -> makeDeclaration s ms
  Just (n, fz) -> (n, ms { position = fz :<+>: fs})

nearestSource :: MachineState -> Source
nearestSource ms@(MS { position = fz :<+>: _}) = go fz
  where
    go B0 = error "Impossible : no enclosing Source frame"
    go (fz :< Source src) = src
    go (fz :< _) = go fz

onNearestSource :: ([Tok] -> [Tok]) -> MachineState -> MachineState
onNearestSource f ms@(MS { position = fz :<+>: fs}) = ms{ position = go fz :<+>: fs }
  where
    go B0 = error "Impossible : no enclosing Source frame"
    go (fz :< Source (n, Hide ts)) = fz :< Source (n, Hide $ f ts)
    go (fz :< f) = go fz :< f

run :: MachineState -> MachineState
run ms@(MS { position = fz :<+>: [], problem = p })
  | File (cs :<=: src) <- p = case fundecls ms B0 cs of
      (ms, fz') -> run $ ms { position = fz <> fz' :< Locale ScriptLocale :< Source src :<+>: [] , problem = BlockTop cs }
  | BlockTop ((c :<=: src):cs) <- p = run $ ms { position = fz :< BlockRest cs :< Source src :<+>: [] , problem = Command c }
  | LHS (LVar x) <- p = case ensureDeclaration (UserDecl x True [] True) ms of
      (n, ms) -> move $ ms { problem = Done (FreeVar n) }
  | LHS (LMat []) <- p = move $ ms { problem = Done nil }
  | FormalParam x <- p = case makeDeclaration (UserDecl x True [] False) ms of
      (n, ms) -> move $ ms { problem = Done (FreeVar n) }
  | Expression (Var x) <- p = case findDeclaration (UserDecl x True [] False) fz of
      Nothing -> move $ ms { problem = Done (yikes (T $^ atom "OutOfScope" <&> atom x)) }
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
  | Expression (IntLiteral i) <- p = move $ ms { problem = Done (lit i) }
  | Expression (DoubleLiteral d) <- p = move $ ms { problem = Done (lit d) }
  | Expression (StringLiteral s) <- p = move $ ms { problem = Done (lit s) }
  | Expression (UnaryOp op (e :<=: src)) <- p = run $ ms { position = fz :< Source src :<+>: [], problem = Expression e }
  | Expression (BinaryOp op (e0 :<=: src0) e1) <- p = run $ ms { position = fz :< Expressions [e1] :< Source src0 :<+>: [], problem = Expression e0 }
  | Expression ColonAlone <- p = move $ ms { problem = Done (atom ":") }
  | Expression (Handle f) <- p = move $ ms { problem = Done (T $^ atom "handle" <&> atom f) }
  | FunCalled f <- p = run $ ms { problem = Expression f }
--  | Expression (Lambda xs t) <- p = _
  | Row rs <- p = case rs of
      [] -> move $ ms { problem = Done nil }
      ((r :<=: src):rs) -> run $ ms { position = fz :< Expressions rs :< Source src :<+>: [], problem = Expression r }
  | Command (Assign lhs (e :<=: src)) <- p = run $ ms { position = fz :< TargetLHS lhs :< Source src :<+>: [] , problem = Expression e }
  | Command (Direct rl ((Rename old new :<=: src, _) :<=: src')) <- p = run $ ms { position = fz :< Source src' :< Source src :<+>: [] , problem = RenameAction old new rl}
  | Command (Direct rl ((InputFormat name :<=: src, Just (InputFormatBody body)) :<=: src')) <- p = run $ ms { position = fz :< Source src' :< Source src :<+>: [] , problem = InputFormatAction name body rl}
  | Command (Function (lhs, fname :<=: _, args) cs) <- p = case findDeclaration (UserDecl fname True [] False) fz of
      Nothing -> error "function should have been declared already"
      Just (fname, fz) -> case fundecls ms B0 cs of
            (ms, fz') -> move $ ms { position = (fz <> fz') :< Locale FunctionLocale :< FunctionLeft fname lhs :< BlockRest cs :< FormalParams args :<+>: [] , problem = Done nil }
  | Command (Respond ts) <- p = move $ onNearestSource (const []) (ms { problem = Done nil })
  | Command (GeneratedCode cs) <- p = move $ onNearestSource (const []) (ms { problem = Done nil })
  | Command (If brs els) <- p = let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els
      in move $ ms { position = fz :< Conditionals conds :<+>: [], problem = Done nil }
  | Command (For (x, e :<=: src) cs) <- p = run $ ms { position = fz :< BlockRest cs :< TargetLHS (LVar <$> x) :< Source src :<+>: [], problem = Expression e }
  | Command (While e cs) <- p = move $ ms { position = fz :< Conditionals [(e, cs)] :<+>: [], problem = Done nil }
  | Command Break <- p =  move $ ms { problem = Done nil}
  | Command Continue <- p =  move $ ms { problem = Done nil}
  | Command Return <- p = move $ ms { problem = Done nil}
  | Command (Switch (exp :<=: src) brs els) <- p = let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els -- TODO: handle `otherwise` responsibly
      in run $ ms { position = fz :< Conditionals conds :< Source src :<+>: [], problem = Expression exp }
--  | Command (GeneratedCode cs) <- p = _wY
  | RenameAction old new rl <- p = case ensureDeclaration (UserDecl old False [(new, rl)] True) ms of
      (n, ms) -> move $ ms { problem = Done nil}
  | InputFormatAction name body (n, c) <- p = move $ ms { nonceTable = Map.insertWith (++) n (concat ["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) (nonceTable ms)
                                                   , problem = Done nil}
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
  | TargetLHS (lhs :<=: src) <- fr = run $
    ms { position = fz :< Fork (Right Solved) fs (Done t) :< Source src :<+>: [], problem = LHS lhs }
  | Conditionals conds <- fr = case conds of
      [] -> move $ ms { position = fz :< Fork (Right Solved) fs (Done t) :<+>: [], problem = Done nil }
      ((e :<=: src, cs) : conds) -> run $
        ms { position = fz :< Fork (Right Solved) fs (Done t) :< Conditionals conds :< BlockRest cs :< Source src :<+>: [], problem = Expression e }
  | FormalParams params <- fr = case params of
      [] -> move $ ms { position = fz :< Fork (Right Solved) fs (Done t) :<+>: [], problem = Done nil }
      (p :<=: src) : ps -> run $
        ms { position = fz :< Fork (Right Solved) fs (Done t) :< FormalParams ps :< Source src :<+>: [], problem = FormalParam p}
move ms@(MS { position = fz :< fr :<+>: fs, problem = Done t }) = move $ ms { position = fz :<+>: fr : fs }
move ms = ms

generateInputReader :: String -> [String] -> String
generateInputReader name body = case translateString Matlab name (concat (init body)) of
  Left err -> "% Error: " ++ show err
  Right s -> s

fundecls :: MachineState -> Bwd Frame -> [Command] -> (MachineState, Bwd Frame)
fundecls ms fz [] = (ms, fz)
fundecls ms fz (Function (_, fname :<=: _ , _) _ :<=: src:cs) = case freshNames [fname ++ "Type", fname] ms of
  ([ty, n], ms) -> let def = Definition ty (Zy, VN) Nothing (atom SType)
                       decl = Declaration n (FreeVar ty) (UserDecl fname False [] False)
                       in fundecls ms (fz :< def :< decl) cs
fundecls ms fz (c:cs) = fundecls ms fz cs
