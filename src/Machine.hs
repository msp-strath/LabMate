module Machine where

import Control.Monad
import Control.Newtype
import Control.Monad.State
import Data.Char
import Data.List
import Data.Maybe (fromMaybe, isNothing)
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
import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace

debug = const id --trace

type Elab = State MachineState

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , nameSupply :: (Root, Int)
  , nonceTable :: Map Nonce String
  , metaStore :: Store
  , constraintStore :: Map Name Constraint
  , clock :: Int
  , epoch :: Int
  } deriving Show


initMachine :: File -> Map Nonce String -> MachineState
initMachine f t = MS
  { position = B0 :<+>: []
  , problem = File f
  , nameSupply = (B0 :< ("labmate", 0), 0)
  , nonceTable = t
  , metaStore = Map.empty
  , constraintStore = Map.empty
  , clock = 0
  , epoch = 0
  }

type TERM = Term Chk ^ Z
type TYPE = Type ^ Z

data DiagnosticData
  = SynthD
      TYPE {- T -}
      TERM {- t :: T -}
      Expr {- e, t = elab e -}
  deriving Show

data Frame where
  Source :: Source -> Frame
  Declaration :: Name -> DeclarationType TYPE -> Frame
  Locale :: LocaleType -> Frame
  ExcursionReturnMarker :: Frame
  RenameFrame :: String -> String -> Frame
  FunctionLeft :: Name -> LHS -> Frame
  Fork :: (Either Fork Fork) -> [Frame] -> Problem -> Frame
  Problems :: [Problem] -> Frame
  LocalNamespace :: NameSupply -> Frame
  Diagnostic :: DiagnosticData -> ResponseLocation -> Frame
  deriving Show

data Fork = Solved | FunctionName Name
  deriving Show

data LocaleType = ScriptLocale | FunctionLocale
  deriving (Show, Eq)

data DeclarationType a
  = UserDecl
  { varTy :: a             -- (eventual) type
  , currentName :: String  -- current name
  , seen :: Bool           -- have we seen it in user code?
  -- requested name and how to reply (we hope of length at most 1)
  , newNames :: [(String, ResponseLocation)]
  , capturable :: Bool     -- is it capturable?
  }
  | LabmateDecl
  deriving (Functor, Show, Foldable, Traversable)


data ElabTask where
  TensorTask :: TensorType' -> ElabTask
  TypeExprTask :: TypeExpr' -> ElabTask
  LHSTask :: LHS' -> ElabTask
  ExprTask :: Expr' -> ElabTask
  Await :: NATTY n => ConstraintStatus -> Term Chk ^ n -> ElabTask
  Abandon :: ElabTask -> ElabTask
deriving instance Show ElabTask

data Problem where
  File :: File -> Problem
  BlockTop :: [Command] -> Problem
  Command :: Command' -> Problem
  LHS :: LHS' -> Problem
  FormalParam :: String -> Problem
  Done :: TERM -> Problem
  Expression :: Expr' -> Problem
  Row :: [Expr] -> Problem
  RenameAction :: String -> String -> ResponseLocation -> Problem
  DeclareAction :: TERM -> String -> Problem
  InputFormatAction :: String -> [String] -> ResponseLocation -> Problem
  FunCalled :: Expr' -> Problem
  Elab :: Name -> ElabTask -> Problem
  Sourced :: WithSource Problem -> Problem
  deriving (Show)

data Lit
  = IntLit Int
  | DoubleLit Double
  | StringLit String
  deriving Show

data Gripe =
  RenameFail Nonce String
  deriving Show

elabTC :: Context n -> TC n x -> Elab (Either String x)
elabTC ctx tc = do
  store <- gets metaStore
  pure $ runTC tc store ctx

fresh :: String -> Elab Name
fresh s = do
  (r, n) <- gets nameSupply
  modify $ \st -> st { nameSupply = (r, n + 1) }
  pure $ name (r, n) s

pull :: Elab (Maybe Frame)
pull = gets position >>= \case
  B0 :<+>: _ -> pure Nothing
  fz :< fr :<+>: fs -> Just fr <$ modify (\st -> st { position = fz :<+>: fs })

push :: Frame -> Elab ()
push f = do
  modify $ \st@MS{ position = fz :<+>: fs } -> st { position = fz :< f :<+>: fs }

llup :: Elab (Maybe Frame)
llup = gets position >>= \case
  _ :<+>: [] -> pure Nothing
  fz :<+>: fr : fs -> Just fr <$ modify (\st -> st { position = fz :<+>: fs })

shup :: Frame -> Elab ()
shup f = do
  modify $ \st@MS{ position = fz :<+>: fs } -> st { position = fz :<+>: f : fs }

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
  st@MS{..} <- get
  let fz :<+>: fs = position
  put $ st { position = fz :<+>: fs', problem = p' }
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
newProb p = modify (\st -> st{ problem = p })

swapNameSupply :: NameSupply -> Elab NameSupply
swapNameSupply ns = do
  ns' <- gets nameSupply
  modify $ \st -> st { nameSupply = ns }
  pure ns'

newNamespace :: String -> Elab NameSupply
newNamespace s = do
  (root, n) <- gets nameSupply
  modify $ \st -> st { nameSupply = (root, n + 1) }
  pure (root :< (s, n), 0)

localNamespace :: String -> Elab ()
localNamespace s = do
  ns <- newNamespace s
  ns <- swapNameSupply ns
  push $ LocalNamespace ns

getMeta :: Name -> Elab Meta
getMeta x = do
  st <- gets metaStore
  case Map.lookup x st of
    Just m -> pure m
    Nothing -> error "getMeta: meta does not exist"

cry :: Name -> Elab ()
cry x = do
  meta <- getMeta x
  modify $ \st@MS{..} -> st { metaStore = Map.insert x (meta{ mstat = Crying }) metaStore }

yikes :: TERM -> TERM
yikes t = T $^ atom "yikes" <&> t

tick :: Elab ()
tick =  modify $ \st@MS{..} -> st { clock = clock + 1 }

data ConstraintType n
  = Hom (Type ^ n)
  -- heterogenous constraint will become homogenous as soon as the
  -- named constraints have been solved
  | Het (Type ^ n) [Name] (Type ^ n)
  deriving Show

lhsType :: ConstraintType n -> Type ^ n
rhsType :: ConstraintType n -> Type ^ n

lhsType (Hom ty) = ty
lhsType (Het lty _ _) = lty

rhsType (Hom ty) = ty
rhsType (Het _ _ rty) = rty

isHom :: ConstraintType n -> Maybe (Type ^ n)
isHom (Hom ty) = Just ty
isHom _ = Nothing

data ConstraintStatus
  = Impossible
  | Blocked
  | SolvedIf [Name] -- the constraints has been reduced to the
                    -- conjuction of the named constraints
  | Unstarted
  deriving Show

instance Semigroup ConstraintStatus where
  (<>) = mappend

instance Monoid ConstraintStatus where
  mempty = SolvedIf []

  mappend Impossible _ = Impossible
  mappend _ Impossible = Impossible
  mappend Blocked _    = Blocked
  mappend _ Blocked    = Blocked
  mappend Unstarted y  = Unstarted
  mappend x Unstarted  = Unstarted
  mappend (SolvedIf xs) (SolvedIf ys) = SolvedIf $ xs `union` ys

data Constraint = forall n . Constraint
  { constraintCtx   :: Vec n (String, ConstraintType n)
  , constraintType  :: ConstraintType n
  , constraintStatus :: ConstraintStatus
  , lhs :: Term Chk ^ n
  , rhs :: Term Chk ^ n
  }

instance (Show Constraint) where
  show Constraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", constraintType = ", show constraintType
    , ", status = ", show constraintStatus
    , ", lhs = ", show lhs
    , ", rhs = ", show rhs
    , " }"
    ]

normalise :: Context n -> Type ^ n -> Term Chk ^ n -> Elab (Norm Chk ^ n)
normalise ctx ty tm  = elabTC ctx (checkEval ty tm) >>= \case
  Left err -> error $ "normalise : TC error" ++ err
  Right tm -> pure tm

normaliseDiagnostic :: DiagnosticData -> Elab DiagnosticData
normaliseDiagnostic (SynthD ty tm e) = do
  ty <- normalise emptyContext (atom SType) ty
  tm <- normalise emptyContext ty tm
  pure $ SynthD ty tm e

constrain :: String -> Constraint -> Elab ConstraintStatus
constrain s c@Constraint{..} = debug ("Constrain call " ++ s ++ " constraint = " ++ show c) $ case (traverse (traverse isHom) constraintCtx, constraintType) of
  (Just ctx, Hom ty) -> nattily (vlen constraintCtx) $ do
    ms  <- gets metaStore
    ty  <- normalise ctx (atom SType) ty
    lhs <- normalise ctx ty lhs
    rhs <- normalise ctx ty rhs
    case debug ("CONSTRAIN " ++ show lhs ++ " = " ++ show rhs) (lhs, rhs) of
      _ | debug "Checking syntactic equality?" (lhs == rhs) -> debug ("Passed syn eq for " ++ show lhs ++ " =?= " ++ show rhs) (pure $ SolvedIf [])
      (E :$ (M (x, n) :$ sig) :^ th, t :^ ph)
        | Just meta@Meta{..} <- x `Map.lookup` ms
        , Hoping <- mstat
        , Right Refl <- idSubstEh sig
        , Just ph <- ph `thicken` th
        , x `Set.notMember` dependencies t ->
          case nattyEqEh n (vlen mctxt) of
            Just Refl -> do
              metaDefn x (t :^ ph)
              pure $ SolvedIf []
            _ -> error "constrain: different context lengths"
      (t :^ ph, E :$ (M (x, n) :$ sig) :^ th)
        | Just meta@Meta{..} <- x `Map.lookup` ms
        , Hoping <- mstat
        , Right Refl <- idSubstEh sig
        , Just ph <- ph `thicken` th
        , x `Set.notMember` dependencies t ->
          case nattyEqEh n (vlen mctxt) of
            Just Refl -> do
              metaDefn x (t :^ ph)
              pure $ SolvedIf []
            _ -> error "constrain: different context lengths"
      -- different atoms are never unifiable, raise the constraint as impossible
      _ | Just (s1, []) <- tagEh lhs
        , Just (s2, []) <- tagEh rhs
        , s1 /= s2 -> do
            s <- fresh s
            modify $ \st@MS{..} -> st{ constraintStore = Map.insert s c{constraintStatus = Impossible} constraintStore }
            pure Impossible
      _ | Just (lt, ls) <- tagEh lhs
        , Just (rt, rs) <- tagEh rhs
        , lt == rt -> case (lt, ls, rs) of
          (SDest, [lty], [rty]) -> constrain s $ Constraint
            { constraintCtx = constraintCtx
            , constraintType = constraintType
            , constraintStatus = constraintStatus
            , lhs = lty
            , rhs = rty
            }
          _ -> do
            s <- fresh s
            modify $ \st@MS{..} -> st{ constraintStore = Map.insert s c constraintStore }
            pure $ case constraintStatus of
              Blocked   -> SolvedIf [s]
              Unstarted -> SolvedIf [s]
              _ -> constraintStatus
      _ -> do
       s <- fresh s
       modify $ \st@MS{..} -> st{ constraintStore = Map.insert s c constraintStore }
       pure $ case constraintStatus of
         Blocked   -> SolvedIf [s]
         Unstarted -> SolvedIf [s]
         _ -> constraintStatus
  _ -> do
    s <- fresh s
    modify $ \st@MS{..} -> st{ constraintStore = Map.insert s c constraintStore }
    pure $ case constraintStatus of
      Blocked   -> SolvedIf [s]
      Unstarted -> SolvedIf [s]
      _ -> constraintStatus

constrainEqualType :: TYPE -> TYPE -> Elab ()
constrainEqualType lhs rhs = (() <$) . constrain "Q" $ Constraint
  { constraintCtx   = VN
  , constraintType  = Hom (atom SType)
  , constraintStatus = Unstarted
  , lhs = lhs
  , rhs = rhs
  }

getConstraintStatus :: Name -> Elab ConstraintStatus
getConstraintStatus x = do
  cstore <- gets constraintStore
  case constraintStatus <$> Map.lookup x cstore of
    Nothing -> pure Impossible
    Just Blocked -> pure $ SolvedIf [x]
    Just (SolvedIf xs) -> mconcat <$> traverse getConstraintStatus xs
    Just cstatus -> pure cstatus

updateConstraintStatus :: ConstraintStatus -> Elab ConstraintStatus
updateConstraintStatus (SolvedIf xs) =
  mconcat <$> traverse getConstraintStatus xs
updateConstraintStatus cs = pure cs

findDeclaration :: DeclarationType (Maybe TYPE) -> Elab (Maybe (Name, TYPE))
findDeclaration LabmateDecl = pure Nothing
findDeclaration UserDecl{varTy = ty, currentName = old, seen, newNames = news} = excursion (go False)
  where
  go :: Bool {- we think we are in a function -} -> Elab (Maybe (Name, TYPE))
  go b = pull >>= \case
    Nothing -> pure Nothing
    Just f -> case f of
      Locale ScriptLocale | b -> -- if we are in a function, script
        Nothing <$ push f        -- variables are out of scope
      Locale FunctionLocale -> shup f >> go True -- we know we are in a function
      Declaration n u'@UserDecl{varTy = ty', currentName = old', seen = seen', newNames = news'} | old == old' -> do
        case ty of
          Just ty -> constrainEqualType ty ty'
          Nothing -> pure ()
        Just (n, ty') <$ push (Declaration n u'{seen = seen' || seen, newNames = news' ++ news})
      _ -> shup f >> go b

makeDeclaration :: DeclarationType TYPE -> Elab (Name, TYPE)
makeDeclaration LabmateDecl = error "making labmatedecl declaration"
makeDeclaration d@UserDecl{varTy, currentName} = excursion $ do
  findLocale
  x <- fresh currentName
  (x, varTy) <$ push (Declaration x d)
  where
    findLocale = pull >>= \case
      Nothing -> error "Locale disappeared!"
      Just f  -> shup f >> case f of
        Locale{} -> pure ()
        _ -> findLocale

ensureDeclaration :: DeclarationType (Maybe TYPE) -> Elab (Name, TYPE)
ensureDeclaration s = findDeclaration s >>= \case
  Nothing -> ensureType s >>= makeDeclaration
  Just x  -> pure x

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
   x <$ modify (\st@MS{..} -> st { metaStore = Map.insert x (Meta ctx ty Nothing s) metaStore })

metaDeclTerm :: Status -> String -> Context n -> Type ^ n -> Elab (Term Chk ^ n)
metaDeclTerm s x ctx ty = nattily (vlen ctx) (wrapMeta <$> metaDecl s x ctx ty)

metaDefn :: Name -> Term Chk ^ n -> Elab ()
metaDefn x def = getMeta x >>= \case
  Meta{..}
    | Just Refl <- scopeOf def `nattyEqEh` vlen mctxt
    , mstat `elem` [Waiting, Hoping] -> do
      tick
      modify $ \st@MS{..} -> st{ metaStore = Map.insert x (Meta mctxt mtype (Just def) mstat) metaStore}
  _ -> error "metaDefn: check the status or the scope"

invent :: String -> Context n -> Type ^ n -> Elab (Term Chk ^ n)
invent x ctx ty = nattily (vlen ctx) $ normalise ctx (atom SType) ty >>= \case
  ty
    | Just (SOne, []) <- tagEh ty ->
      pure nil
    | Just (SPi, [s, t]) <- tagEh ty, Just (y, t) <- lamNameEh t ->
      lam y <$> invent x (ctx \\\ (y, s)) t
    | Just (SSig, [s, t]) <- tagEh ty, Just (y, t) <- lamNameEh t -> do
        a <- invent x ctx s
        d <- invent x ctx (t //^ sub0 (R $^ a <&> s))
        pure (T $^ a <&> d)
  ty -> wrapMeta <$> metaDecl Hoping x ctx ty

ensureType :: DeclarationType (Maybe TYPE) -> Elab (DeclarationType TYPE)
ensureType LabmateDecl = error "ensureType: cannot invent type for labmate decl."
ensureType dt@UserDecl{varTy, currentName} = do
  ty <- case varTy of
    Nothing  -> invent (currentName ++ "Type") emptyContext (atom SType)
    Just ty  -> pure ty
  pure $ dt {varTy = ty}

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
    (x, _) <- ensureDeclaration (UserDecl Nothing x True [] True)
    newProb . Done $ FreeVar x
    move
  LHS (LMat []) -> do
    newProb $ Done nil
    move
  FormalParam x -> do
    ty <- invent (x ++ "Type") emptyContext (atom SType)
    (x, _) <- makeDeclaration (UserDecl ty x True [] False)
    newProb . Done $ FreeVar x
    move
  Expression (Var x) ->
    findDeclaration (UserDecl Nothing x True [] False) >>= \case
    Nothing -> do
      newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
      move
    Just (x, _) -> do
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
  Expression (Handle f) -> newProb (Done $ T $^ atom "handle" <&> atom f) >> move
  FunCalled f -> newProb (Expression f) >> run
  Row rs -> case rs of
    [] -> newProb (Done nil) >> move
    (r :<=: src):rs -> do
      traverse_ push [Problems (Sourced . fmap Expression <$> rs), Source src]
      newProb $ Expression r
      run
  Command (Assign lhs rhs) -> do
    ty <- invent "assignTy" emptyContext (atom SType)
    (_, lhsProb) <- elab "AssignLHS" emptyContext (mk SDest ty) (LHSTask <$> lhs)
    (_, rhsProb) <- elab "AssignRHS" emptyContext ty (ExprTask <$> rhs)
    push $ Problems [lhsProb]
    newProb rhsProb
    run
  Command (Direct rl (dir :<=: src)) -> do
    push $ Source src
    runDirective rl dir
  Command (Function (lhs, fname :<=: _, args) cs) ->
    findDeclaration (UserDecl Nothing fname True [] False)  >>= \case
      Nothing -> error "function should have been declared already"
      Just (fname, _) -> do
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
    ensureDeclaration (UserDecl Nothing old False [(new, rl)] True)
    newProb $ Done nil
    move
  DeclareAction ty name -> do
    (name, _) <- ensureDeclaration (UserDecl (Just ty) name False [] True)
    newProb $ Done (FreeVar name)
    move
  InputFormatAction name body (n, c) -> do
    modify $ \st@MS{..} -> st { nonceTable = Map.insertWith (++) n (concat["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) nonceTable }
    newProb $ Done nil
    move
  Elab name etask -> do
    meta <- getMeta name
    runElabTask name meta etask
  Sourced (p :<=: src) -> do
    localNamespace . take 10 . filter isAlpha $ show p
    push $ Source src
    newProb p
    run
  -- _ -> trace ("Falling through. Problem = " ++ show (problem ms)) $ move
  _ -> move

runDirective :: ResponseLocation -> Dir' -> Elab ()
runDirective rl (dir :<=: src, body) = do
  push $ Source src
  case dir of
    Rename old new -> do
      newProb $ RenameAction old new rl
      run
    InputFormat name | Just (InputFormatBody body) <- body -> do
      newProb $ InputFormatAction name body rl
      run
    Declare xs ty -> do
      (sol, prob) <- elab "declType" emptyContext (atom SType) (TensorTask <$> ty)
      push $ Problems (Sourced . fmap (DeclareAction sol) <$> xs)
      newProb prob
      run
    Typecheck ty e -> do
      (tySol, tyProb) <- elab "typeToCheck" emptyContext (atom SType) (TensorTask <$> ty)
      (eSol, eProb) <- elab "exprToCheck" emptyContext tySol (ExprTask <$> e)
      --traverse push [Diagnostic _ rl, Problems [eProb]]
      newProb tyProb
      run
    SynthType e -> do
      ty <- invent "typeToSynth" emptyContext (atom SType)
      (eSol, eProb) <- elab "exprToSynth" emptyContext ty (ExprTask <$> e)
      push $ Diagnostic (SynthD ty eSol e) rl
      newProb eProb
      run
    _ -> move

elab'
  :: String -- name advice for new elaboration prob
  -> Context n
  -> Type ^ n -- the type of the solution
  -> ElabTask
  -> Elab (Term Chk ^ n, Problem)
elab' x ctx ty etask = nattily (vlen ctx) $ do
  x <- metaDecl Waiting x ctx ty
  pure (wrapMeta x, Elab x etask)

elab
  :: String -- name advice for new elaboration prob
  -> Context n
  -> Type ^ n -- the type of the solution
  -> WithSource ElabTask
  -> Elab (Term Chk ^ n, Problem)
elab x ctx ty (etask :<=: src) =
  fmap (Sourced . (:<=: src)) <$> elab' x ctx ty etask

runElabTask :: Name -> Meta -> ElabTask -> Elab ()
runElabTask sol meta@Meta{..} etask = nattily (vlen mctxt) $ do
  mtype <- normalise mctxt (atom SType) mtype
  case etask of
    TensorTask (Tensor ((x, xs :<=: xSrc), (y, ys :<=: ySrc)) (eTy :<=: eSrc)) -> do
      xTy <- invent (x ++ "Type") mctxt (atom SType)
      yTy <- invent (y ++ "Type") mctxt (atom SType)
      (xsSol, xsProb) <- elab (x ++ "List") mctxt (mk SList xTy) (TypeExprTask xs :<=: xSrc)
      (ysSol, ysProb) <- elab (y ++ "List") mctxt (mk SList yTy) (TypeExprTask ys :<=: ySrc)
      let ctx = mctxt \\\ (x, xTy) \\\ (y, wk yTy)
      (eSol, eProb) <- elab "entryType" ctx (atom SType) (TypeExprTask eTy :<=: eSrc)
      push $ Problems [xsProb, ysProb, eProb]
      metaDefn sol (mk SMatrix xTy yTy (lam x . lam y $ eSol) xsSol ysSol)
      newProb $ Done nil
      move
    TypeExprTask (TyVar Lint) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SAbel (atom SOne) -< no (vlen mctxt)
      newProb $ Done nil
      move
    TypeExprTask (TyVar Lstring) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SList (atom SChar) -< no (vlen mctxt)
      newProb $ Done nil
      move
    TypeExprTask (TyVar x) -> -- TODO: check whether `x` is already present in the mctxt, i.e. shadowing
      findDeclaration (UserDecl Nothing x True [] False) >>= \case
        Nothing -> do
          newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
          cry sol
          move
        Just (x, xty) -> do
          -- TODO: to solve `sol` with the current value of `x`
          constrain "VarExpr" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (atom SType)
            , constraintStatus = Unstarted
            , lhs = xty -< no natty
            , rhs = mtype
            }
          newProb . Done $ FreeVar x
          move
    TypeExprTask (TyNum k) -> case tagEh mtype of
      Just (SList, [genTy]) -> do
        cs <- constrain "IsOne" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , constraintStatus = Unstarted
          , lhs = genTy
          , rhs = atom SOne
          }
        case () of
          _ | k >= 0 -> do
            newProb . Elab sol $ Await cs (ixKI mtype (lit k))
          _ | True -> do
            cry sol
            newProb . Elab sol $ Abandon etask
        run
      Just (SAbel, [genTy]) -> do
        cs <- constrain "IsOne" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , constraintStatus = Unstarted
          , lhs = genTy
          , rhs = atom SOne
          }
        newProb . Elab sol $ Await cs (ixKI mtype (lit k))
        run
      Just (SMatrix, [rowTy, colTy, cellTy, rs, cs])
        | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy -> do
          r <- invent r mctxt rowTy
          c <- invent c mctxt colTy
          rcs <- constrain "IsSingletonR" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList rowTy)
            , constraintStatus = Unstarted
            , lhs = mk Sone r
            , rhs = rs
            }
          ccs <- constrain "IsSingletonC" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList colTy)
            , constraintStatus = Unstarted
            , lhs = mk Sone c
            , rhs = cs
            }
          (cellSol, cellProb) <- elab' "cell" mctxt (cellTy //^ subSnoc (sub0 (R $^ r <&> rowTy)) (R $^ c <&> colTy)) etask
          push $ Problems [cellProb]
          newProb . Elab sol $ Await (rcs <> ccs) (mk Sone cellSol)
          run
      _ -> move
    TypeExprTask (TyBinaryOp Plus x y) -> do
      -- TODO:
      -- 1. make sure `mtype` admits plus
      -- 2. find the correct way of doing plus in `mtype`
      (xSol, xProb) <- elab "plusXTy" mctxt mtype (TypeExprTask <$> x)
      (ySol, yProb) <- elab "plusYTy" mctxt mtype (TypeExprTask <$> y)
      push $ Problems [xProb, yProb]
      newProb . Done $ nil -- FIXME: use the solutions
      move
    TypeExprTask (TyStringLiteral s) -> case tagEh mtype of
      Just (SList, [genTy]) -> do
        cs <- constrain "IsChar" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , constraintStatus = Unstarted
          , lhs = genTy
          , rhs = atom SChar
          }
        newProb . Elab sol $ Await cs (ixKI mtype (lit s))
        run
      _ -> move
    LHSTask lhs -> case lhs of
      LVar x -> do
        (x, ty) <- debug ("Lvar " ++ show meta) $ ensureDeclaration (UserDecl Nothing x True [] True)
        ccs <- constrain "IsLHSTy" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , constraintStatus = Unstarted
          , lhs = mk SDest (ty -< no (vlen mctxt))
          , rhs = mtype
          }
        newProb . Done $ FreeVar x
        move
      _ -> do  -- switch to being a scoping problem
        newProb $ LHS lhs
        run
    ExprTask e -> case toTypeExpr' e of
      Just e -> do
        newProb . Elab sol $ TypeExprTask e
        run
      _ -> do  -- switch to being a scoping problem
        newProb $ Expression e
        run
    Await cstatus tm -> updateConstraintStatus cstatus >>= \case
      SolvedIf [] -> do
        metaDefn sol tm
        newProb $ Done nil
        move
      Impossible -> do
        cry sol
        newProb . Elab sol $ Abandon etask
        move
      cstatus -> do
        newProb . Elab sol $ Await cstatus tm
        move
    _ -> move

-- if move sees a Left fork, it should switch to Right and run
-- if move sees a Right fork, switch to Left and keep moving
move :: Elab ()
move = pull >>= \case
  Nothing -> do
    cleanup
    st@MS{..} <- get
    if (clock > epoch)
      then do
        put st{ epoch = clock }
        run
      else do
        diagnosticPass
  Just fr -> case fr of
    Fork (Right frk) fs' p' -> do
      (fs, p) <- switchFwrd (fs', p')
      shup $ Fork (Left frk) fs p
      move
    Fork (Left frk) fs' p' -> do
      (fs, p) <- switchFwrd (fs', p')
      push $ Fork (Right frk) fs p
      run
    Declaration x xty -> do  -- propagate information from solved
                             -- metavars before we clean them up
      xty <- traverse (normalise emptyContext (atom SType)) xty
      shup (Declaration x xty)
      move
    Diagnostic dd rl -> do
      dd <- normaliseDiagnostic dd
      shup (Diagnostic dd rl)
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

cleanup :: Elab ()
cleanup = do
  ms <- gets metaStore
  flip Map.traverseWithKey ms $ \name meta@Meta{..} -> nattily (vlen mctxt) $ do
    ctx <- traverse (traverse (normalise mctxt (atom SType))) mctxt
    ty <- normalise ctx (atom SType) mtype
    tm <- traverse (normalise ctx ty) mdefn
    let meta = Meta{ mctxt = ctx, mtype = ty, mdefn = tm, mstat = mstat }
    modify $ \st@MS{..} -> st{ metaStore = Map.insert name meta metaStore }
  modify $ \st@MS{..} -> st{ metaStore = Map.filter (\Meta{..} -> mstat /= Hoping || isNothing mdefn) metaStore }


diagnosticPass :: Elab ()
diagnosticPass = do
  st <- get

generateInputReader :: String -- ^
  -> [String] -- ^
  -> String
generateInputReader name body = case translateString Matlab name (concat (init body)) of
  Left err -> "% Error: " ++ show err
  Right s -> s

fundecl :: Command -> Elab ()
fundecl (Function (_, fname :<=: _ , _) _ :<=: _) = do
  ty <- invent (fname ++ "Type") emptyContext (atom SType)
  fname' <- metaDecl Hoping fname emptyContext ty
  push $ Declaration fname' (UserDecl ty fname False [] False)
fundecl _ = pure ()
