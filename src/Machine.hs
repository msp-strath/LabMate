module Machine where

import Control.Monad
import Control.Newtype
import Control.Monad.State
import Data.Char
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
  Just (LocalNamespace ns) -> do
    oldNs <- swapNameSupply ns
    push $ LocalNamespace oldNs
    prob
  Just f  -> push f >> prob

newProb :: Problem -> Elab () -- TODO: consider checking if we are at
                              -- the problem
newProb p = modify (\ms -> ms{ problem = p })

swapNameSupply :: NameSupply -> Elab NameSupply
swapNameSupply ns = do
  ns' <- gets nameSupply
  modify $ \ms -> ms { nameSupply = ns }
  pure ns'

newNamespace :: String -> Elab NameSupply
newNamespace s = do
  (root, n) <- gets nameSupply
  modify $ \ms -> ms { nameSupply = (root, n + 1) }
  pure (root :< (s, n), 0)

localNamespace :: String -> Elab ()
localNamespace s = do
  ns <- newNamespace s
  ns <- swapNameSupply ns
  push $ LocalNamespace ns

type TERM = Term Chk ^ Z
type TYPE = Type ^ Z

data Frame where
  Source :: Source -> Frame
  Declaration :: Name -> TYPE -> DeclarationType -> Frame
  Definition :: Name -> Status -> Frame
  Locale :: LocaleType -> Frame
  ExcursionReturnMarker :: Frame
  RenameFrame :: String -> String -> Frame
  FunctionLeft :: Name -> LHS -> Frame
  Fork :: (Either Fork Fork) -> [Frame] -> Problem -> Frame
  Problems :: [Problem] -> Frame
  LocalNamespace :: NameSupply -> Frame
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
  | DeclareAction String
  | InputFormatAction String [String] ResponseLocation
  | FunCalled Expr'
  | Sourced (WithSource Problem)
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
  BlockTop cs -> do
    push $ Problems (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move
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
    traverse_ push [Problems (Sourced . fmap Expression <$> args), Source src]
    newProb $ FunCalled f
    run
  Expression (Brp (e :<=: src) args) -> do
    traverse_ push [Problems (Sourced . fmap Expression <$> args), Source src]
    newProb $ Expression e
    run
  Expression (Dot (e :<=: src) fld) -> do
    push $ Source src
    newProb $ Expression e
    run
  Expression (Mat es) -> do
    push $ Problems (Row <$> es)
    newProb $ Done nil
    move
  Expression (IntLiteral i) -> newProb (Done $ lit i) >> move
  Expression (DoubleLiteral d) -> newProb (Done $ lit d) >> move
  Expression (StringLiteral s) -> newProb (Done $ lit s) >> move
  Expression (UnaryOp op (e :<=: src)) -> do
    push $ Source src
    newProb $ Expression e
    run
  Expression (BinaryOp op (e0 :<=: src0) e1) -> do
    traverse_ push [Problems [Sourced (Expression <$> e1)], Source src0]
    newProb $ Expression e0
    run
  Expression ColonAlone -> newProb (Done $ atom ":") >> move
  Expression (Handle f) -> newProb ( Done $ T $^ atom "handle" <&> atom f) >> move
  FunCalled f -> newProb (Expression f) >> run
  Row rs -> case rs of
    [] -> newProb (Done nil) >> move
    (r :<=: src):rs -> do
      traverse_ push [Problems (Sourced . fmap Expression <$> rs), Source src]
      newProb $ Expression r
      run
  Command (Assign lhs (e :<=: src)) -> do
    traverse_ push [Problems [Sourced (LHS <$> lhs)], Source src]
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
  Command (Direct rl ((Declare xs ty :<=: src, _) :<=: src')) -> do
    traverse_ push [Source src', Source src]
    push $ Problems (Sourced . fmap DeclareAction <$> xs)
    newProb $ Done nil -- FIXME
    move
  Command (Function (lhs, fname :<=: _, args) cs) ->
    findDeclaration (UserDecl fname True [] False)  >>= \case
      Nothing -> error "function should have been declared already"
      Just fname -> do
        traverse_ fundecl cs
        traverse_ push [ Locale FunctionLocale
                       , FunctionLeft fname lhs
                       , Problems (Sourced . fmap Command <$> cs)
                       , Problems (Sourced . fmap FormalParam <$> args)
                       ]
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
    push . Problems $ conds >>= \(e, cs) -> Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move
  Command (For (x, e :<=: src) cs) -> do
    traverse_ push [Problems (Sourced. fmap Command <$> cs), Problems [Sourced (LHS . LVar <$> x)], Source src]
    newProb $ Expression e
    run
  Command (While e cs) -> do
    push . Problems $ Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move
  Command Break -> newProb (Done nil) >> move
  Command Continue -> newProb (Done nil) >> move
  Command Return -> newProb (Done nil) >> move
  Command (Switch exp brs els) -> do
    let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els -- TODO: handle `otherwise` responsibly
    push . Problems $ conds >>= \(e, cs) ->  Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Sourced (Expression <$> exp)
    run
  RenameAction old new rl -> do
    ensureDeclaration (UserDecl old False [(new, rl)] True)
    newProb $ Done nil
    move
  DeclareAction name -> do
    name <- ensureDeclaration (UserDecl name False [] True)
    newProb $ Done (FreeVar name)
    move
  InputFormatAction name body (n, c) -> do
    modify $ \ms@MS{..} -> ms { nonceTable = Map.insertWith (++) n (concat["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) nonceTable }
    newProb $ Done nil
    move
  Sourced (p :<=: src) -> do
    localNamespace . take 10 . filter isAlpha $ show p
    push $ Source src
    newProb p
    run
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
    FunctionLeft fname (lhs :<=: src) -> do
      (fs, p) <- switchFwrd ([], LHS lhs)
      traverse_ push [Fork (Right $ FunctionName fname) fs p, Source src]
      run
    Problems [] -> do
      (fs, p) <- switchFwrd ([], Done nil)
      push $ Fork (Right Solved) fs p
      move
    Problems (p : ps) -> do
      (fs, p) <- switchFwrd ([], p)
      traverse_ push [Fork (Right Solved) fs p, Problems ps]
      run
    LocalNamespace ns -> do
      ns <- swapNameSupply ns
      shup $ LocalNamespace ns
      move
    _ -> shup fr >> move

generateInputReader :: String -> [String] -> String
generateInputReader name body = case translateString Matlab name (concat (init body)) of
  Left err -> "% Error: " ++ show err
  Right s -> s

fundecl :: Command -> Elab ()
fundecl (Function (_, fname :<=: _ , _) _ :<=: _) = do
  ty <- metaDeclTerm Hoping (fname++"Type") emptyContext (atom SType)
  fname' <- metaDecl Hoping fname emptyContext ty
  push (Declaration fname' ty (UserDecl fname False [] False))
fundecl _ = pure ()
