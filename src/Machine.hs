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
import CoreTT
import Term
import MagicStrings
import Data.Maybe (fromMaybe)

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , nameSupply :: (Root, Int)
  , nonceTable :: Map Nonce String
  , metaStore :: Store
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
  Definition :: Name -> Status -> Frame
  Locale :: LocaleType -> Frame
  ExcursionReturnMarker :: Frame
  Expressions :: [Expr] -> Frame
  TargetLHS :: LHS -> Frame
  Conditionals :: [(Expr, [Command])] -> Frame
  MatrixRows :: [[Expr]] -> Frame
  RenameFrame :: String -> String -> Frame
  FunctionLeft :: Name -> LHS -> Frame
  FormalParams :: [WithSource String] -> Frame
  Fork :: (Either Fork Fork) -> [Frame] -> Problem -> Frame
  deriving Show

data Status = Crying | Waiting | Hoping | Defined
  deriving Show

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
  , metaStore = Map.empty
  }

findDeclaration :: DeclarationType -> MachineState -> Maybe (Name, MachineState)
findDeclaration LabmateDecl ms = Nothing
findDeclaration (UserDecl old seen news _) ms@MS{position = fz :<+>: fs} =
  fmap (\fz -> ms{position = fz :<+>: fs}) <$> go fz False where
  go B0 _ = Nothing
  go (fz :< Locale ScriptLocale) True = Nothing
  go (fz :< f@(Locale FunctionLocale)) _ = fmap (:< f) <$> go fz True
  go (fz :< f@(Declaration n ty (UserDecl old' seen' news' capturable'))) b | old == old' =
    Just (n , fz :< Declaration n ty (UserDecl old' (seen' || seen) (news' ++ news) capturable'))
  go (fz :< f) b = fmap (:< f) <$> go fz b

makeDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
makeDeclaration LabmateDecl = error "making labmatedecl declaration"
makeDeclaration d@(UserDecl x seen news capturable) = excursion $ \ms ->
  case metaDeclTerm Hoping (x++"Type") emptyContext (atom SType) (findLocale ms) of
    (ty, ms) -> case fresh x ms of
      (x, ms) -> (x, push (Declaration x ty d) ms)
  where
    findLocale ms@MS{ position = B0 :<+>: _ } = error "Locale disappeared!"
    findLocale ms@MS{ position = fz :< f :<+>: fs } =
      ($ ms{ position = fz :<+>: f : fs }) $ case f of
        Locale{} -> id
        _ -> findLocale

ensureDeclaration :: DeclarationType -> MachineState -> (Name, MachineState)
ensureDeclaration s ms = fromMaybe (makeDeclaration s ms) (findDeclaration s ms)

nearestSource :: MachineState -> Source
nearestSource ms@(MS { position = fz :<+>: _}) = go fz
  where
    go B0 = error "Impossible: no enclosing Source frame"
    go (fz :< Source src) = src
    go (fz :< _) = go fz

onNearestSource :: ([Tok] -> [Tok]) -> MachineState -> MachineState
onNearestSource f ms@(MS { position = fz :<+>: fs}) = ms{ position = go fz :<+>: fs }
  where
    go B0 = error "Impossible: no enclosing Source frame"
    go (fz :< Source (n, Hide ts)) = fz :< Source (n, Hide $ f ts)
    go (fz :< f) = go fz :< f

metaDecl :: Status -> String -> Context n -> Type ^ n -> MachineState -> (Name, MachineState)
metaDecl s x ctx ty ms@MS {position = fz :<+>: fs, metaStore = mstore} = case fresh x ms of
  (x, ms) -> (x, ms{ position = fz :< Definition x s :<+>: fs
                   , metaStore = Map.insert x (Meta ctx ty Nothing) mstore
                   }
             )

metaDeclTerm :: Status -> String -> Context n -> Type ^ n -> MachineState -> (Term Chk ^ n, MachineState)
metaDeclTerm s x ctx@(n, c) ty ms = case metaDecl s x ctx ty ms of
  (x, ms) -> (E $^ M (x, n) $^ (idSubst n :^ io n), ms)

push :: Frame -> MachineState -> MachineState
push f ms@MS{ position = fz :<+>: fs } = ms { position = fz :< f :<+>: fs }

pushes :: [Frame] -> MachineState -> MachineState
pushes = flip $ foldl (flip push)

excursion
  :: (MachineState -> (v, MachineState)) -- the operation should leave the cursor to the left of where it started
  -> MachineState
  -> (v, MachineState)
excursion op ms@MS{ position = fz :<+>: fs } = case op ms{ position = fz :<+>: (ExcursionReturnMarker : fs) } of
  (v, ms@MS{..}) -> (v, ms{position = go position}) where
    go :: Cursor Frame -> Cursor Frame
    go (fz :<+>: ExcursionReturnMarker : fs) = fz :<+>: fs
    go (fz :<+>: f : fs) = go (fz :< f :<+>: fs)
    go (fz :<+>: []) = error "excursion got lost"

run :: MachineState -> MachineState
run ms@(MS { position = fz :<+>: [], problem = p })
  | File (cs :<=: src) <- p = case fundecls cs ms of
      ms -> run $ (pushes [Locale ScriptLocale, Source src] ms) { problem = BlockTop cs }
  | BlockTop ((c :<=: src):cs) <- p = run $ ms { position = fz :< BlockRest cs :< Source src :<+>: [] , problem = Command c }
  | LHS (LVar x) <- p = case ensureDeclaration (UserDecl x True [] True) ms of
      (x, ms) -> move $ ms { problem = Done (FreeVar x) }
  | LHS (LMat []) <- p = move $ ms { problem = Done nil }
  | FormalParam x <- p = case makeDeclaration (UserDecl x True [] False) ms of
      (x, ms) -> move $ ms { problem = Done (FreeVar x) }
  | Expression (Var x) <- p = case findDeclaration (UserDecl x True [] False) ms of
      Nothing -> move $ ms { problem = Done (yikes (T $^ atom "OutOfScope" <&> atom x)) }
      Just (x, ms)  -> move $ ms { problem = Done (FreeVar x) }
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
  | Command (Function (lhs, fname :<=: _, args) cs) <- p = case findDeclaration (UserDecl fname True [] False) ms of
      Nothing -> error "function should have been declared already"
      Just (fname, ms) -> case fundecls cs ms of
        ms -> move $ (pushes [Locale FunctionLocale, FunctionLeft fname lhs, BlockRest cs, FormalParams args] ms) { problem = Done nil }
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
  | InputFormatAction name body (n, c) <- p = move $ ms { nonceTable = Map.insertWith (++) n (concat["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) (nonceTable ms), problem = Done nil}
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

fundecls :: [Command] -> MachineState -> MachineState
fundecls [] ms = ms
fundecls (Function (_, fname :<=: _ , _) _ :<=: src:cs) ms =
  case metaDeclTerm Hoping (fname++"Type") emptyContext (atom SType) ms of
    (ty, ms) -> case metaDecl Hoping fname emptyContext ty ms of
      (fname', ms) -> fundecls cs $ push (Declaration fname' ty (UserDecl fname False [] False)) ms
fundecls (_:cs) ms = fundecls cs ms
