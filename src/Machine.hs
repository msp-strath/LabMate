module Machine where

import Control.Monad
import Control.Newtype
import Control.Monad.State
import Data.List
import Data.Maybe (fromMaybe)
import Data.Monoid
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
import Data.Foldable (traverse_)

type Elab = State MachineState

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , nameSupply :: (Root, Int)
  , nonceTable :: Map Nonce String
  , metaStore :: Store
  } deriving Show

fresh :: String -> Elab Name
fresh s = do
  (r, n) <- gets nameSupply
  modify $ \ms -> ms { nameSupply = (r, n + 1) }
  pure $ name (r, n) s

pull :: Elab (Maybe Frame)
pull = gets position >>= \case
  B0 :<+>: _ -> pure Nothing
  fz :< fr :<+>: fs -> Just fr <$ modify (\ms -> ms { position = fz :<+>: fs })

push :: Frame -> Elab ()
push f = do
  modify $ \ms@MS{ position = fz :<+>: fs } -> ms { position = fz :< f :<+>: fs }

llup :: Elab (Maybe Frame)
llup = gets position >>= \case
  _ :<+>: [] -> pure Nothing
  fz :<+>: fr : fs -> Just fr <$ modify (\ms -> ms { position = fz :<+>: fs })

shup :: Frame -> Elab ()
shup f = do
  modify $ \ms@MS{ position = fz :<+>: fs } -> ms { position = fz :<+>: f : fs }

excursion
  :: Elab v -- the operation should leave the cursor to the left of where it started
  -> Elab v
excursion op = do
  shup ExcursionReturnMarker
  v <- op
  v <$ go
  where
    go = llup >>= \case
      Just ExcursionReturnMarker -> pure ()
      Just fr -> push fr >> go
      Nothing -> error "excursion got lost"

switchFwrd :: ([Frame], Problem) -> Elab ([Frame], Problem)
switchFwrd (fs', p') = do
  ms@MS{..} <- get
  let fz :<+>: fs = position
  put $ ms { position = fz :<+>: fs', problem = p' }
  pure (fs, problem)

prob :: Elab Problem
prob = llup >>= \case
  Nothing -> gets problem
  Just f  -> push f >> prob

newProb :: Problem -> Elab () -- TODO: consider checking if we are at
                              -- the problem
newProb p = modify (\ms -> ms{ problem = p })

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

findDeclaration :: DeclarationType -> Elab (Maybe Name)
findDeclaration LabmateDecl = pure Nothing
findDeclaration (UserDecl old seen news _)  = excursion (go False)
  where
  go :: Bool {- we think we are in a function -} -> Elab (Maybe Name)
  go b = pull >>= \case
    Nothing -> pure Nothing
    Just f -> case f of
      Locale ScriptLocale | b -> -- if we are in a function, script
        Nothing <$ push f        -- variables are out of scope
      Locale FunctionLocale -> shup f >> go True -- we know we are in a function
      Declaration n ty (UserDecl old' seen' news' capturable') | old == old' ->
        Just n <$ push (Declaration n ty (UserDecl old' (seen' || seen) (news' ++ news) capturable'))
      _ -> shup f >> go b

makeDeclaration :: DeclarationType -> Elab Name
makeDeclaration LabmateDecl = error "making labmatedecl declaration"
makeDeclaration d@(UserDecl x seen news capturable) = excursion $ do
  findLocale
  ty <- metaDeclTerm Hoping (x++"Type") emptyContext (atom SType)
  x <- fresh x
  x <$ push (Declaration x ty d)
  where
    findLocale = pull >>= \case
      Nothing -> error "Locale disappeared!"
      Just f  -> shup f >> case f of
        Locale{} -> pure ()
        _ -> findLocale

ensureDeclaration :: DeclarationType -> Elab Name
ensureDeclaration s = findDeclaration s >>= \case
  Nothing -> makeDeclaration s
  Just x -> pure x

onNearestSource :: ([Tok] -> [Tok]) -> Elab ()
onNearestSource f = excursion go
  where
    go = pull >>= \case
      Nothing -> error "Impossible: no enclosing Source frame"
      Just (Source (n, Hide ts)) -> push $ Source (n, Hide $ f ts)
      Just f -> shup f >> go

metaDecl :: Status -> String -> Context n -> Type ^ n -> Elab Name
metaDecl s x ctx ty = do
   x <- fresh x
   push $ Definition x s
   x <$ modify (\ms@MS{..} -> ms { metaStore = Map.insert x (Meta ctx ty Nothing) metaStore})

metaDeclTerm :: Status -> String -> Context n -> Type ^ n -> Elab (Term Chk ^ n)
metaDeclTerm s x ctx@(n, c) ty = wrap <$> metaDecl s x ctx ty
  where
  wrap x = E $^ M (x, n) $^ (idSubst n :^ io n)

run :: Elab ()
run = prob >>= \case
  File (cs :<=: src) -> do
    traverse_ fundecl cs
    traverse_ push [Locale ScriptLocale, Source src]
    newProb $ BlockTop cs
    run
  BlockTop ((c :<=: src):cs) -> do
    traverse_ push [BlockRest cs, Source src]
    newProb $ Command c
    run
  LHS (LVar x) -> do
    x <- ensureDeclaration (UserDecl x True [] True)
    newProb . Done $ FreeVar x
    move
  LHS (LMat []) -> do
    newProb $ Done nil
    move
  FormalParam x -> do
    x <- makeDeclaration (UserDecl x True [] False)
    newProb . Done $ FreeVar x
    move
  Expression (Var x) ->
    findDeclaration (UserDecl x True [] False) >>= \case
    Nothing -> do
      newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
      move
    Just x -> do
      newProb . Done $ FreeVar x
      move
  Expression (App (f :<=: src) args) -> do
    traverse_ push [Expressions args, Source src]
    newProb $ FunCalled f
    run
  Expression (Brp (e :<=: src) args) -> do
    traverse_ push [Expressions args, Source src]
    newProb $ Expression e
    run
  Expression (Dot (e :<=: src) fld) -> do
    push $ Source src
    newProb $ Expression e
    run
  Expression (Mat es) -> case es of
    [] -> newProb (Done nil) >> run
    (r:rs) -> do
      push $ MatrixRows rs
      newProb $ Row r
      run
  Expression (Cell es) -> case es of
    [] -> newProb (Done nil) >> run
    (r:rs) -> do
      push $ MatrixRows rs
      newProb $ Row r
      run
  Expression (IntLiteral i) -> newProb (Done $ lit i) >> move
  Expression (DoubleLiteral d) -> newProb (Done $ lit d) >> move
  Expression (StringLiteral s) -> newProb (Done $ lit s) >> move
  Expression (UnaryOp op (e :<=: src)) -> do
    push $ Source src
    newProb $ Expression e
    run
  Expression (BinaryOp op (e0 :<=: src0) e1) -> do
    traverse_ push [Expressions [e1], Source src0]
    newProb $ Expression e0
    run
  Expression ColonAlone -> newProb (Done $ atom ":") >> move
  Expression (Handle f) -> newProb ( Done $ T $^ atom "handle" <&> atom f) >> move
  FunCalled f -> newProb (Expression f) >> run
--  | Expression (Lambda xs t) <- p = _
  Row rs -> case rs of
    [] -> newProb (Done nil) >> move
    (r :<=: src):rs -> do
      traverse_ push [Expressions rs, Source src]
      newProb $ Expression r
      run
  Command (Assign lhs (e :<=: src)) -> do
    traverse_ push [TargetLHS lhs, Source src]
    newProb $ Expression e
    run
  Command (Direct rl ((Rename old new :<=: src, _) :<=: src')) -> do
    traverse_ push [Source src', Source src]
    newProb $ RenameAction old new rl
    run
  Command (Direct rl ((InputFormat name :<=: src, Just (InputFormatBody body)) :<=: src')) -> do
    traverse_ push [Source src', Source src]
    newProb $ InputFormatAction name body rl
    run
  Command (Function (lhs, fname :<=: _, args) cs) ->
    findDeclaration (UserDecl fname True [] False)  >>= \case
      Nothing -> error "function should have been declared already"
      Just fname -> do
        traverse_ fundecl cs
        traverse_ push [Locale FunctionLocale, FunctionLeft fname lhs, BlockRest cs, FormalParams args]
        newProb $ Done nil
        move
  Command (Respond ts) -> do
    onNearestSource $ const []
    newProb $ Done nil
    move
  Command (GeneratedCode cs) -> do
    onNearestSource $ const []
    newProb $ Done nil
    move
  Command (If brs els) -> do
    let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els
    push $ Conditionals conds
    newProb $ Done nil
    move
  Command (For (x, e :<=: src) cs) -> do
    traverse_ push [BlockRest cs, TargetLHS (LVar <$> x), Source src]
    newProb $ Expression e
    run
  Command (While e cs) -> do
    push $ Conditionals [(e, cs)]
    newProb $ Done nil
    move
  Command Break -> newProb (Done nil) >> move
  Command Continue -> newProb (Done nil) >> move
  Command Return -> newProb (Done nil) >> move
  Command (Switch (exp :<=: src) brs els) -> do
    let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els -- TODO: handle `otherwise` responsibly
    traverse_ push [Conditionals conds, Source src]
    newProb $ Expression exp
    run
  RenameAction old new rl -> do
    ensureDeclaration (UserDecl old False [(new, rl)] True)
    newProb $ Done nil
    move
  InputFormatAction name body (n, c) -> do
    modify $ \ms@MS{..} -> ms { nonceTable = Map.insertWith (++) n (concat["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) nonceTable }
    newProb $ Done nil
    move
  -- _ -> trace ("Falling through. Problem = " ++ show (problem ms)) $ move
  _ -> move



-- if move sees a Left fork, it should switch to Right and run
-- if move sees a Right fork, switch to Left and keep moving
move :: Elab ()
move = pull >>= \case
  Nothing -> pure ()
  Just fr -> case fr of
    Fork (Right frk) fs' p' -> do
     (fs, p) <- switchFwrd (fs', p')
     shup $ Fork (Left frk) fs p
     move
    BlockRest [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    BlockRest ((c :<=: src): cs) -> do
      (fs, p) <- switchFwrd ([], Command c)
      traverse_ push [Fork (Right Solved) fs p, BlockRest cs, Source src]
      run
    Expressions [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    Expressions ((e :<=: src):es) -> do
      (fs, p) <- switchFwrd ([], Expression e)
      traverse_ push [Fork (Right Solved) fs p, Expressions es, Source src]
      run
    MatrixRows [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    MatrixRows (r : rs) -> do
      (fs, p) <- switchFwrd ([], Row r)
      traverse_ push [Fork (Right Solved) fs p, MatrixRows rs]
      run
    FunctionLeft fname (lhs :<=: src) -> do
      (fs, p) <- switchFwrd ([], LHS lhs)
      traverse_ push [Fork (Right $ FunctionName fname) fs p, Source src]
      run
    TargetLHS (lhs :<=: src) -> do
      (fs, p) <- switchFwrd ([], LHS lhs)
      traverse_ push [Fork (Right Solved) fs p, Source src]
      run
    Conditionals [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    Conditionals ((e :<=: src, cs) : conds) -> do
      (fs, p) <- switchFwrd ([], Expression e)
      traverse_ push [Fork (Right Solved) fs p, Conditionals conds, BlockRest cs, Source src]
      run
    FormalParams [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    FormalParams ((p :<=: src) : ps) -> do
      (fs, p) <- switchFwrd ([], FormalParam p)
      traverse_ push [Fork (Right Solved) fs p, FormalParams ps, Source src]
      run
    _ -> shup fr >> move

generateInputReader :: String -> [String] -> String
generateInputReader name body = case translateString Matlab name (concat (init body)) of
  Left err -> "% Error: " ++ show err
  Right s -> s

fundecl :: Command -> Elab ()
fundecl (Function (_, fname :<=: _ , _) _ :<=: src) = do
  ty <- metaDeclTerm Hoping (fname++"Type") emptyContext (atom SType)
  fname' <- metaDecl Hoping fname emptyContext ty
  push (Declaration fname' ty (UserDecl fname False [] False))
fundecl _ = pure ()
