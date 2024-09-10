module Machine where

import GHC.Stack

import Control.Monad
import Control.Newtype
import Control.Monad.State
import Data.Char
import Data.Either
import Data.List
import Data.Maybe (fromMaybe, isNothing)
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import Data.Traversable

-- mgen
import TranslateContext (TargetLang(..))
import Translate

import MissingLibrary

import Bwd
import Term.Indexed

import Lex
import Parse
import Parse.Matlab
import Syntax
import Hide
import CoreTT
import NormalForm
import Term
import MagicStrings
import Data.Foldable (traverse_)
import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace
import Control.Monad.Reader

debug = const id -- trace
debugCatch = const id -- trace
debugMatrix = const id -- trace
debug260824 = trace

type Elab = State MachineState

data MachineState = MS
  { position :: Cursor Frame
  , problem :: Problem
  , nameSupply :: (Root, Int)
  , nonceTable :: Map Nonce String
  , refoldingMap :: Map TYPE String -- shitty version
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
  , refoldingMap = Map.empty
  , metaStore = Map.empty
  , constraintStore = Map.empty
  , clock = 0
  , epoch = 0
  }

-- whatever PPMonad is, it should have Monoid instance which lifts the
-- monoid structure of values
type PPMonad = (->) Name

class PrettyPrint t where
  -- the list of strings must be non-empty
  pprint :: t -> PPMonad [String]

pptm :: TERM -> PPMonad String
pptm tm = do
  ns <- ask
  pure $ tmShow False tm (ns, VN)

dent :: [String] -> [String]
dent [] = []
dent (s : ss) = ("+-" ++ s) : map ("| " ++) ss

instance PrettyPrint ([Frame], Problem) where
  pprint ([], p) = pprint p
  pprint (f : fs, p) = case f of
    LocalNamespace (root, _) -> do
      let d = Name (root <>> [])
      ld <- localName d
      pure [ld ++ " |-" ] <> local (const d) (pprint (fs, p))
    Fork (Left frk) ->
      (dent <$> pprint (fs, p)) <> pprint frk
    Fork (Right frk) ->
      (dent <$> pprint frk) <> pprint (fs, p)
    _ -> pprint f <> pprint (fs, p)

instance PrettyPrint Fork where
  pprint MkFork{..} = tweak fstatus <$> pprint (fframes, fprob) where
    tweak (Winning True ()) = id
    tweak (Winning False ()) = ("???" :)
    tweak Whacked = ("%%%" :)

instance PrettyPrint ElabTask where
  -- TODO: implement
  pprint = pure . (:[]) . show

instance PrettyPrint Problem where
  pprint (Done tm) = (:[]) . ("Done " ++) <$> pptm tm
  pprint (Elab n x) = do
    ln <- localName n
    zipWith (++) ((ln ++ " <- ") : repeat "  ") <$> pprint x
  pprint p = pure [show p]

instance PrettyPrint DiagnosticData where
  pprint (SynthD ty tm (exp :<=: (n, _))) = do
    ty <- pptm ty
    tm <- pptm tm
    pure [tm ++ " :: " ++ ty ++ " <- $" ++ show n]
  pprint (UnitD un stat tn) = do
    stat <- pptm stat
    pure ["unit $" ++ show un ++ " " ++ stat ++ " $" ++ show tn]
  pprint (UnitDs units) =
    pure ["units" ++ foldMap (\u -> " $" ++ show (nonce u)) units]
  pprint (ReadFromD filename vars) =
    pure ["readfrom" ++ filename ++ " " ++ show vars]

instance PrettyPrint Frame where
  pprint (Declaration n UserDecl{..}) = do
    dn <- localName n
    tm <- pptm varTy
    pure [dn ++ " := " ++ currentName ++ " :: " ++ tm]
  pprint (Currently ty lhs rhs) = do
    ty <- pptm ty
    lhs <- pptm lhs
    rhs <- pptm rhs
    pure ["Currently " ++ lhs ++ " = " ++ rhs ++ " :: " ++ ty]
  pprint (Diagnostic (n, _) d) =
    zipWith (++) (("Diagnostic $" ++ show n ++ " ") : repeat "  ") <$> pprint d
  pprint (Source (n, Hide ts)) = pure [concat ["$", show n, ": ", ts >>= blat]]
   where
     blat t | Non n <- kin t = '$': show n
     blat t = raw t
  pprint (ConstraintFrame n c) = pure ["!CONSTRAINT FRAME!", show n ++ "  " ++ show c]
  pprint fr = pure [show fr]

instance PrettyPrint MachineState where
  pprint st = do
    let (fz :<+>: fs) = position st
    lines <- pprint (fz <>> fs, problem st)
    pure ({-show (metaStore st) : show (constraintStore st) :-} lines)

type TERM = Term Chk ^ Z
type TYPE = Typ ^ Z
type BOOL = Norm Chk ^ Z

data DiagnosticData
  = SynthD
      TYPE {- T -}
      TERM {- t :: T -}
      Expr {- e, t = elab e -}
  | UnitD Nonce BOOL Nonce
  | UnitDs [WithSource String]
  | ReadFromD String [Either String (String, TYPE)]
  deriving Show

data Frame where
  Source :: Source -> Frame
  Declaration :: Name -> DeclarationType TYPE -> Frame
  Definition :: Name -> TERM -> Frame -- should have a corresponding declaration
  Locale :: LocaleType -> Frame
  ExcursionReturnMarker :: Frame
  RenameFrame :: String -> String -> Frame
  -- FunctionLeft :: Name -> LHS -> Frame
  -- conjunctive interpretation
  Fork :: (Either Fork Fork) -> Frame
  -- disjunctive interpretation
  Catch :: Fork -> Frame
  LocalNamespace :: NameSupply -> Frame
  Diagnostic :: ResponseLocation -> DiagnosticData -> Frame
  Currently
    :: TYPE -- T
    -> TERM -- lhs, a metavar of type Dest T
    -> TERM -- rhs
    -> Frame
  LocalStore :: Store -> Frame
  ConstraintFrame :: Name -> Constraint -> Frame
  deriving Show

data Fork = MkFork
  { fstatus :: ForkCompleteStatus
  , fframes :: [Frame]
  , fprob   :: Problem
  } deriving Show

data LocaleType = ScriptLocale | FunctionLocale Name
  deriving (Show, Eq)

--Unify `Mood` and `ForkCompleteStatus` as:

data Mood' a
  = Whacked
  | Winning Bool {- have we completely won yet -} a
  deriving (Functor, Foldable, Traversable, Show, Ord, Eq)

type Mood = Mood' Store
type ForkCompleteStatus = Mood' ()

instance Semigroup ForkCompleteStatus where
  (<>) = mappend

instance Monoid ForkCompleteStatus where
  mempty = winning
  mappend = min

-- linear in the store, paying attention to the way things can get worse
andMood :: Mood' Store -> Mood' () -> (Mood' Store, Maybe Store)
andMood (Winning _ st) Whacked = (Whacked, Just st)
andMood (Winning True st) (Winning False ()) = (Winning False st, Nothing)
andMood m _ = (m, Nothing)

-- When we are moving through a `Fork`, `andMood` should tell us how
-- the status of the other conjuncts affects our mood and whether we
-- should contain a local store.

winning :: Monoid a => Mood' a
winning = Winning True mempty

worried :: Monoid a => Mood' a
worried = Winning False mempty


data WhereAmI = MatLab | LabMate
  deriving (Show, Eq, Ord)

data SynthesisMode = FindSimplest | EnsureCompatibility
  deriving (Eq, Show)

data DeclarationType a
  = UserDecl
  { varTy :: a             -- (eventual) type
  , currentName :: String  -- current name
  , seen :: Bool           -- have we seen it in user code?
  -- requested name and how to reply (we hope of length at most 1)
  , newNames :: [(String, ResponseLocation)]
  , capturable :: Bool     -- is it capturable?
  , whereAmI :: WhereAmI   -- LabMate variables are not in scope for MatLab
  }
  deriving (Functor, Show, Foldable, Traversable)


data ElabTask where
  TensorTask :: TensorType' -> ElabTask
  TypeExprTask :: WhereAmI -> SynthesisMode -> TypeExpr' -> ElabTask
  LHSTask :: LHS' -> ElabTask
  ExprTask :: WhereAmI -> SynthesisMode -> Expr' -> ElabTask
  Await :: NATTY n
    => BOOL          -- the closed Boolean value we hope will become true
    -> Term Chk ^ n  -- the scoped solution we will commit if the
                     -- Boolean becomes true
    -> ElabTask
  ConstrainTask :: NATTY n => WhereAmI -> (String, Constraint) -> [BOOL] -> Term Chk ^ n -> ElabTask
  ElimTask :: NATTY n => Natty n -> (Term Chk ^ n, Typ ^ n) -> [TypeExpr] -> ElabTask
  AbelTask :: TypeExpr' -> ElabTask -- the problem type must be Abel genTy for some genTy
  ConstantCellTask :: SynthesisMode -> TypeExpr' -> ElabTask
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
  Prefer :: Problem -> Problem -> Problem
  Whack :: Problem
  Worry :: Problem
  Sourced :: WithSource Problem -> Problem
  Problems :: [Problem] -> Problem
  deriving Show

data Lit
  = IntLit Int
  | DoubleLit Double
  | StringLit String
  deriving Show

data Gripe =
  RenameFail Nonce String
  deriving Show

modifyNearestStore :: (Store -> Store) -> Elab ()
modifyNearestStore f = excursion go where
  go = pull >>= \case
    Nothing -> modify (\st@MS{..} -> st { metaStore = f metaStore })
    Just (LocalStore st) -> push $ LocalStore (f st)
    Just fr -> shup fr >> go

-- TODO: cache the accumulated stores
elabTC :: Context n -> TC n x -> Elab (Either String x)
elabTC ctx tc = do
  store <- gets metaStore
  fz :<+>: fs <- gets position
  let accStores = ala' Dual foldMap frameToStore fz
  pure $ runTC tc (accStores <> store) ctx
  where
    frameToStore :: Frame -> Store
    frameToStore (LocalStore st) = debug ("Local store: " ++ intercalate ", " (show <$> Map.keys st)) st
    frameToStore _ = mempty


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

pullUntil :: s -> (s -> Frame -> Either s t) -> Elab (Maybe t)
pullUntil s f = pull >>= \case
  Nothing -> pure Nothing
  Just fr -> do
    shup fr
    case f s fr of
      Right t -> pure $ Just t
      Left  s -> pullUntil s f

postRight :: [Frame] -> Elab ()
postRight fs = pull >>= \case
  Nothing -> error "Not in a left fork, is it a hard fail?"
  Just (Fork (Left frk@MkFork{..})) ->
    push $ Fork (Left frk{ fstatus = foldMap getStatus fs <> fstatus
                         , fframes = fs ++ fframes})
  Just fr -> shup fr >> postRight fs
  where
    getStatus (Fork frk) = either fstatus fstatus frk
    getStatus _ = mempty

switchFwrd :: ([Frame], Problem) -> Elab ([Frame], Problem)
switchFwrd (fs', p') = do
  st@MS{..} <- get
  let fz :<+>: fs = position
  put $ st { position = fz :<+>: fs', problem = p' }
  pure (fs, problem)

pushSource :: Source -> Elab ()
pushSource src
  | realSourceEh src = push $ Source src
  | otherwise = pure ()

prob :: Elab Problem
prob = llup >>= \case
  Nothing -> gets problem
  Just (LocalNamespace ns) -> do
    oldNs <- swapNameSupply ns
    push $ LocalNamespace oldNs
    prob
  Just (ConstraintFrame name c) -> do
    c <- updateConstraint c
    debug ("`prob` attempting to solve constraint " ++ show c) $ solveConstraint name c
    prob
  Just f  -> do
    f <- normaliseFrame f
    push f
    prob

pushProblems :: [Problem] -> Elab ()
pushProblems ps = push $ Fork
  (Left MkFork{fstatus = worried, fframes = [], fprob = Problems ps})

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
  fz :<+>: _ <- gets position
  st <- gets metaStore
  let stores = st : foldMap collectStores fz
  case ala' Last foldMap (Map.lookup x) stores of
    Just m -> pure m
    Nothing -> error "getMeta: meta does not exist"
  where
    collectStores (LocalStore st) = [st]
    collectStores _ = []

cry :: HasCallStack => Name -> Elab ()
cry x = do
  meta <- debug (prettyCallStack callStack) $ getMeta x
  modify $ \st@MS{..} -> st { metaStore = Map.insert x (meta{ mstat = Crying }) metaStore }

yikes :: TERM -> TERM
yikes t = T $^ atom "yikes" <&> t

tick :: Elab ()
tick =  modify $ \st@MS{..} -> st { clock = clock + 1 }

data ConstraintType' t
  = Hom t
  -- heterogeneous constraint will become homogeneous as soon as the
  -- Boolean value in the middle becomes true
  | Het t BOOL t
  deriving (Show, Functor)

type ConstraintType n = ConstraintType' (Typ ^ n)

lhsType :: ConstraintType n -> Typ ^ n
rhsType :: ConstraintType n -> Typ ^ n

lhsType (Hom ty) = ty
lhsType (Het lty _ _) = lty

rhsType (Hom ty) = ty
rhsType (Het _ _ rty) = rty

data SimplifiedContext m = forall n. SimplifiedContext
  { simplifiedContext :: ConstraintContext n
  , simplifySubst :: Subst m ^ n -- strengthening
  }

nonUnitTypes :: Vec j (String, ConstraintType m) -> Ex (Flip (<=) j)
nonUnitTypes VN = Ex (Flip Ze)
nonUnitTypes (ga :# (_, cty)) = case nonUnitTypes ga of
  Ex (Flip th) -> case cty of
    Hom t | isUnitType t -> Ex (Flip (No th))
          | otherwise -> Ex (Flip (Su th))

strengthenNil :: i <= j -> Subst j i
strengthenNil Ze = Sub0
strengthenNil (No th) = SubT (strengthenNil th) (leftAll (no (weeEnd th))) (R :$ P (A "" :$ U) ZZ oneTypeZ)
strengthenNil (Su th) = wkSubst (strengthenNil th)

simplifyContext :: ConstraintContext m -> SimplifiedContext m
simplifyContext ga = case nonUnitTypes ga of
  Ex (Flip th) -> let sg = strengthenNil th :^ io (weeEnd th) in
                    SimplifiedContext (fmap (fmap (fmap (//^ sg))) (th ?^ ga)) sg


updateConstraintType :: ConstraintContext n -> ConstraintType n -> Elab (ConstraintType n)
updateConstraintType ctx (Hom t) = nattily (vlen ctx) $ Hom <$> normalise (fmap lhsType <$> ctx) (atom SType) t
updateConstraintType ctx (Het s b t) = nattily (vlen ctx) $ normalise emptyContext (atom STwo) b >>= \case
  Intg 1 -> Hom <$> normalise (fmap lhsType <$> ctx) (atom SType) s
  b -> Het <$> normalise (fmap lhsType <$> ctx) (atom SType) s <*> pure b <*> normalise (fmap rhsType <$> ctx) (atom SType) t

updateConstraint :: Constraint -> Elab Constraint
updateConstraint Constraint{..} = do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  constraintType' <- updateConstraintType constraintCtx constraintType
  case simplifyContext constraintCtx of
    SimplifiedContext constraintCtx sg -> do
      let constraintType = fmap (//^ sg) constraintType'
      lhs <- normalise (fmap lhsType <$> constraintCtx) (lhsType constraintType) (lhs //^ sg)
      rhs <- normalise (fmap rhsType <$> constraintCtx) (rhsType constraintType) (rhs //^ sg)
      pure Constraint{..}
updateConstraint SubtypingConstraint{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  gotType <- normalise (fmap lhsType <$> constraintCtx) (atom SType) gotType
  wantType <- normalise (fmap rhsType <$> constraintCtx) (atom SType) wantType
  pure SubtypingConstraint{..}
updateConstraint SameLength{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let leftCtx = fmap lhsType <$> constraintCtx
  let rightCtx = fmap rhsType <$> constraintCtx
  leftEltType <- normalise leftCtx (atom SType) leftEltType
  rightEltType <- normalise rightCtx (atom SType) rightEltType
  leftList <- normalise leftCtx (mk SList leftEltType) leftList
  rightList <- normalise rightCtx (mk SList rightEltType) rightList
  pure SameLength{..}
updateConstraint InverseQuantities{..}
  | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy
  , Just (ic, invCellTy) <- lamNameEh invCellTy, Just (ir, invCellTy) <- lamNameEh invCellTy
  = nattily (vlen constraintCtx) $ do
    constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
    let ctx = fmap lhsType <$> constraintCtx
    rowGenType <- normalise ctx (atom SType) rowGenType
    colGenType <- normalise ctx (atom SType) colGenType
    let cellCtx = ctx \\\ (r, mk SAbel rowGenType) \\\ (c, wk $ mk SAbel colGenType)
    let invCtx = ctx \\\ (ic, mk SAbel colGenType) \\\ (ir, wk $ mk SAbel rowGenType)
    cellTy <- lam r . lam c <$> normalise cellCtx (atom SType) cellTy
    invCellTy <- lam ic . lam ir <$> normalise invCtx (atom SType) invCellTy
    pure InverseQuantities{..}
updateConstraint Multiplicable{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let ctx = fmap lhsType <$> constraintCtx
  let (rowGenTy, leftMidGenTy, leftCellType) = leftTypes
  let (rightMidGenTy, colGenTy, rightCellType) = rightTypes
  rowGenTy <- normalise ctx (atom SType) rowGenTy
  leftMidGenTy <- normalise ctx (atom SType) leftMidGenTy
  rightMidGenTy <- normalise ctx (atom SType) rightMidGenTy
  colGenTy <- normalise ctx (atom SType) colGenTy
  leftCellType <- normalise (ctx \\\ ("i", mk SAbel rowGenTy) \\\ ("j", wk $ mk SAbel leftMidGenTy)) (atom SType) leftCellType
  rightCellType <- normalise (ctx \\\ ("i", mk SAbel rightMidGenTy) \\\ ("j", wk $ mk SAbel colGenTy)) (atom SType) rightCellType
  let returnCtx = ctx \\\ ("i", mk SAbel rowGenTy) \\\ ("k", wk $ mk SAbel colGenTy)
  returnCellType <- normalise returnCtx (atom SType) returnCellType
  joinGenType <- normalise ctx (atom SType) joinGenType
  joinElement <- normalise ctx (mk SAbel joinGenType) joinElement
  awaitingStatus <- normalise emptyContext (atom STwo) awaitingStatus
  let leftTypes = (rowGenTy, leftMidGenTy, leftCellType)
  let rightTypes = (rightMidGenTy, colGenTy, rightCellType)
  pure Multiplicable{..}
updateConstraint JoinConstraint{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  leftGenType  <- normalise (fmap lhsType <$> constraintCtx) (atom SType) leftGenType
  rightGenType <- normalise (fmap rhsType <$> constraintCtx) (atom SType) rightGenType
  joinTGenype  <- normalise (fmap lhsType <$> constraintCtx) (atom SType) joinGenType
  pure JoinConstraint{..}
updateConstraint HeadersCompatibility{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let leftCtx = fmap lhsType <$> constraintCtx
  let rightCtx = fmap rhsType <$> constraintCtx
  leftGenType <- normalise leftCtx (atom SType) leftGenType
  rightGenType <- normalise rightCtx (atom SType) rightGenType
  joinGenType <- normalise leftCtx (atom SType) joinGenType
  joinStatus <- normalise emptyContext (atom STwo) joinStatus
  leftList <- normalise leftCtx (mk SList (tag SAbel [leftGenType])) leftList
  rightList <- normalise rightCtx (mk SList (tag SAbel [rightGenType])) rightList
  joinElement <- normalise leftCtx (mk SAbel joinGenType) joinElement
  pure HeadersCompatibility{..}
updateConstraint HeaderCompatibility{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let ctx = fmap lhsType <$> constraintCtx
  leftGenType <- normalise ctx (atom SType) leftGenType
  rightGenType <- normalise ctx (atom SType) rightGenType
  joinGenType <- normalise ctx (atom SType) joinGenType
  leftElement <- normalise ctx (mk SAbel leftGenType) leftElement
  rightElement <- normalise ctx (mk SAbel rightGenType) rightElement
  joinElement <- normalise ctx (mk SAbel joinGenType) joinElement
  joinStatus <- normalise emptyContext (atom STwo) joinStatus
  pure HeaderCompatibility{..}
updateConstraint NoMiddleDependency{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let ctx = fmap lhsType <$> constraintCtx
  joinGenStatus <- normalise emptyContext (atom STwo) joinGenStatus
  joinGenType <- normalise ctx (atom SType) joinGenType
  let (i, j, k) = extension
  candidate <- case joinGenStatus of
   Intg 1 -> normalise (ctx \\\ ("i", i) \\\ ("j", wk j) \\\ ("k", wk (wk k))) (mk SAbel (wk (wk (wk joinGenType)))) candidate
   _ -> pure candidate
  pure NoMiddleDependency{..}
updateConstraint ElemConstraint{..} = nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  hayStack <- normalise (fmap lhsType <$> constraintCtx) (mk SList (atom SAtom)) hayStack
  pure ElemConstraint{..}
updateConstraint ListAtomPushout{..} =  nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  let ctx = fmap lhsType <$> constraintCtx
  leftList <- normalise ctx (mk SList (atom SAtom)) leftList
  rightList <- normalise ctx (mk SList (atom SAtom)) rightList
  joinList <- normalise ctx (mk SList (atom SAtom)) joinList
  pure ListAtomPushout{..}
updateConstraint Abel1{..} =  nattily (vlen constraintCtx) $ do
  constraintCtx <- traverse (traverse (updateConstraintType constraintCtx)) constraintCtx
  -- we know that the context is homogeneous
  genType <- normalise (fmap lhsType <$> constraintCtx) (atom SType) genType
  abelExp <- normalise (fmap lhsType <$> constraintCtx) (mk SAbel genType) abelExp
  pure Abel1{..}
updateConstraint c = pure c


isHom :: ConstraintType n -> Maybe (Typ ^ n)
isHom (Hom ty) = Just ty
isHom _ = Nothing

type ConstraintContext n = Vec n (String, ConstraintType n)

data Constraint = forall n . Constraint
  { constraintCtx   :: ConstraintContext n
  , constraintType  :: ConstraintType n
  , lhs :: Term Chk ^ n
  , rhs :: Term Chk ^ n
  }
  | forall n. Multiplicable
  { constraintCtx :: ConstraintContext n
  , leftTypes :: (Typ ^ n, Typ ^ n, Typ ^ S (S n))
  , rightTypes :: (Typ ^ n, Typ ^ n, Typ ^ S (S n))
  , returnCellType :: Typ ^ S (S n)
  , joinGenType :: Typ ^ n
  , joinElement :: Term Chk ^ n
  , awaitingStatus :: BOOL
  }
  | forall n. ElemConstraint
  { constraintCtx :: ConstraintContext n
  , needle :: String
  , hayStack :: Term Chk ^ n
  }
  | forall n . ListAtomPushout
  { constraintCtx :: ConstraintContext n
  , leftList :: Term Chk ^ n
  , rightList :: Term Chk ^ n
  , joinList :: Term Chk ^ n
  }
  | forall n . JoinConstraint
  { constraintCtx :: ConstraintContext n
  , leftGenType :: Term Chk ^ n
  , rightGenType :: Term Chk ^ n
  , joinGenType :: Term Chk ^ n
  }
  | forall n . SubtypingConstraint
  { constraintCtx   :: ConstraintContext n
  , gotType :: Term Chk ^ n
  , wantType :: Term Chk ^ n
  }
  | forall n . HeadersCompatibility
  { constraintCtx :: ConstraintContext n
  , leftGenType :: Term Chk ^ n
  , rightGenType :: Term Chk ^ n
  , joinGenType :: Term Chk ^ n
  , joinStatus :: BOOL
  , leftList :: Term Chk ^ n
  , rightList :: Term Chk ^ n
  , joinElement :: Term Chk ^ n
  }
  | forall n . HeaderCompatibility
  { constraintCtx :: ConstraintContext n
  , leftGenType :: Term Chk ^ n
  , rightGenType :: Term Chk ^ n
  , joinGenType :: Term Chk ^ n
  , joinStatus :: BOOL
  , leftElement :: Term Chk ^ n
  , rightElement :: Term Chk ^ n
  , joinElement :: Term Chk ^ n
  }
  | forall n . NoMiddleDependency
  { constraintCtx :: ConstraintContext n
  , extension :: (Term Chk ^n, Term Chk ^n, Term Chk ^n)
  , joinGenStatus :: BOOL
  , joinGenType :: Term Chk ^ n
  , destination :: Term Chk ^ S (S n)
  , candidate :: Term Chk ^ S (S (S n))
  }
  | forall n . SameLength
  { constraintCtx :: ConstraintContext n
  , leftEltType :: Term Chk ^ n
  , leftList :: Term Chk ^ n
  , rightEltType :: Term Chk ^ n
  , rightList :: Term Chk ^ n
  }
  | forall n . InverseQuantities
  { constraintCtx :: ConstraintContext n
  , rowGenType :: Term Chk ^ n
  , colGenType :: Term Chk ^ n
  , cellTy :: Term Chk ^ n
  , invCellTy :: Term Chk ^ n
  }
  | forall n. Abel1
  { constraintCtx :: ConstraintContext n
  , genType :: Term Chk ^ n
  , abelExp :: Term Chk ^ n
  }
  | DummyConstraint

instance Show Constraint where
  show Constraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", constraintType = ", show constraintType
    , ", lhs = ", show lhs
    , ", rhs = ", show rhs
    , " }"
    ]
  show Multiplicable{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftTypes = ", show leftTypes
    , ", rightTypes = ", show rightTypes
    , ", returnCellType = ", show returnCellType
    , ", joinGenType = ", show joinGenType
    , ", joinElement = ", show joinElement
    , ", awaitingStatus = ", show awaitingStatus
    , " }"
    ]
  show ElemConstraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", needle = ", needle
    , ", hayStack = ", show hayStack
    , " }"
    ]
  show ListAtomPushout{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftList = ", show leftList
    , ", rightList = ", show rightList
    , ", joinList = ", show joinList
    , " }"
    ]
  show JoinConstraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftGenType = ", show leftGenType
    , ", rightGenType = ", show rightGenType
    , ", joinGenType = ", show joinGenType
    , " }"
    ]
  show SubtypingConstraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", gotType = ", show gotType
    , ", wantType = ", show wantType
    , " }"
    ]
  show HeadersCompatibility{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftGenType = ", show leftGenType
    , ", rightGenType = ", show rightGenType
    , ", joinGenType = ", show joinGenType
    , ", joinStatus = ", show joinStatus
    , ", leftList = ", show leftList
    , ", rightList = ", show rightList
    , ", joinElement = ", show joinElement
    , " }"
    ]
  show HeaderCompatibility{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftGenType = ", show leftGenType
    , ", rightGenType = ", show rightGenType
    , ", joinGenType = ", show joinGenType
    , ", joinStatus = ", show joinStatus
    , ", leftElement = ", show leftElement
    , ", rightElement = ", show rightElement
    , ", joinElement = ", show joinElement
    , " }"
    ]
  show NoMiddleDependency{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", extension = ", show extension
    , ", joinGenStatus = ", show joinGenStatus
    , ", joinGenType = ", show joinGenType
    , ", destination = ", show destination
    , ", candidate = ", show candidate
    , " }"
    ]
  show SameLength{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", leftEltType = ", show leftEltType
    , ", leftList = ", show leftList
    , ", rightEltType = ", show rightEltType
    , ", rightList = ", show rightList
    , " }"
    ]
  show InverseQuantities{..}  = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", rowGenType = ", show rowGenType
    , ", colGenType = ", show colGenType
    , ", cellTy = ", show cellTy
    , ", invCellTy = ", show invCellTy
    , " }"
    ]
  show Abel1{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", genType = ", show genType
    , ", abelExp = ", show abelExp
    , " }"
    ]
  show DummyConstraint = "DummyConstraint"


mkConstraintType :: Typ ^ n -> BOOL -> Typ ^ n -> ConstraintType n
mkConstraintType lty (Intg 1) rty = Hom lty
mkConstraintType lty status rty = Het lty status rty

infixl 5 \\\\
(\\\\) :: ConstraintContext n -> (String, ConstraintType n) -> ConstraintContext (S n)
ctx \\\\ x = fmap (fmap wk) <$> ctx :# x

alive :: BOOL -> Bool
alive (Intg 0) = False
alive _ = True

fALSE :: BOOL
fALSE = I 0 :$ U :^ Ze

tRUE :: BOOL
tRUE = I 1 :$ U :^ Ze

conjunction :: [BOOL] -> BOOL
conjunction nfs = case partition isLit nfs of
  (lits, stuck) -> case [() | Intg 0 <- lits] of
    [] -> pack $ Data.List.nub (sort stuck)
    _  -> lit (0 :: Integer)
  where
    pack [] = lit (1 :: Integer)
    pack [nf] = nf
    pack (nf : nfs) = mk Sand nf (pack nfs)

    isLit (Intg _) = True
    isLit _ = False

normalise :: Context n -> Typ ^ n -> Term Chk ^ n -> Elab (Norm Chk ^ n)
normalise ctx ty tm  = elabTC ctx (checkEval ty tm) >>= \case
  Left err -> nattily (vlen ctx) $ error . concat $ ["normalise: TC error [", err, "] for ", show tm, " :: ", show ty]
  Right tm -> pure tm

normalIdSubst :: Context n -> Elab (Subst n ^ n)
normalIdSubst ctx = elabTC ctx (evalSubst (fmap (//^ (sig :^ th)) <$> ctx) (sig :^ th)) >>= \case
    Left err -> error $ "normalIdSubst: " ++ err
    Right sig -> pure sig
  where
    n = vlen ctx
    sig = idSubst n
    th = io n

-- we have successfully detected that one side of the equation is
-- using a flex variable, pack the data to show that; `gamma` is the
-- scope of the constraint
data FlexEh (gamma :: Nat) where
  FlexEh
    :: Name            -- the name of the flex variable
    -> Natty delta     -- the scope of the flex variable
    -> n <= gamma      -- the thinning for the candidate solution's
                       -- permitted dependencies
    -> Subst n ^ delta -- how to map the permitted variables into the
                       -- flex variable's context
    -> FlexEh gamma

data FlexEhWork (gamma' :: Nat)(delta' :: Nat) where
  FlexEhWork
    :: n <= gamma'      -- the thinning for the candidate solution's
                        -- permitted dependencies
    -> Subst n ^ delta' -- how to map the permitted variables into the
                        -- flex variable's context
    -> FlexEhWork gamma' delta'

var0Insert :: S Z <= gamma'  -- we hope this...
           -> n <= gamma'    -- ...is disjoint form these
           -> Subst n ^ delta'
           -> Maybe (FlexEhWork gamma' (S delta'))
var0Insert (Su _) (No ph) (ta :^ ps) = nattily (bigEnd ps) $ Just
  (FlexEhWork (Su ph) (subSnoc (ta :^ No ps) (var 0)))
var0Insert (No up) (No ph) taps = do
  FlexEhWork ph taps <- var0Insert up ph taps
  Just $ FlexEhWork (No ph) taps
var0Insert (No up) (Su ph) (ST :$ P ta u s :^ ps) = do
  FlexEhWork ph tala <- var0Insert up ph (ta :^ (covl u -< ps))
  Just $ FlexEhWork (Su ph) (subSnoc tala (s :^ (No (covr u -< ps))))
var0Insert _ _ _ = Nothing

flexEhWorker
  :: (Context delta, Context gamma, Subst delta ^ gamma)
  -> Vec delta' (String, Typ ^ delta)
  -> Subst delta' gamma'
  -> Vec gamma' (String, Typ ^ gamma)
  -> gamma' <= gamma
  -> Elab (Maybe (FlexEhWork gamma' delta'))
flexEhWorker _ VN Sub0 VN _ = pure . Just $ FlexEhWork Ze (S0 :$ U :^ Ze)
flexEhWorker dg@(delta, gamma, d2g) (delta' :# (x, xTy)) (ST :$ P sg u t) gamma' th = do
  xTy <- withScopeOf xTy $ normalise delta (atom SType) xTy
  flexEhWorker dg delta' sg (covl u ?^ gamma') (covl u -< th) >>= \case
    Nothing -> pure Nothing
    Just (FlexEhWork ph (ta :^ ps)) -> case weeEnd (covr u) of
      Sy (Sy _) -> pure Nothing
      Zy | isUnitType xTy -> pure . Just $ FlexEhWork (ph -< covl u) (ta :^ No ps)
         | otherwise -> pure Nothing
      Sy Zy -> case covr u ?^ gamma' of
        VN :# (y, yTy) -> do
          let up = covr u -< th
          let ytm = E :$ V :^ up
          ytm <- normalise gamma yTy ytm
          t <- normalise gamma (xTy //^ d2g) (E :$ t :^ up)
          if ytm /= t then pure Nothing else pure $ var0Insert (covr u) (ph -< covl u) (ta :^ ps)

flexEh :: Context gamma -> NmTy ^ gamma -> Norm Chk ^ gamma
         -> Elab (Maybe (FlexEh gamma))
flexEh gamma ty (E :$ (M (x, k) :$ sig) :^ th) = do
  ms <- gets metaStore
  case  x `Map.lookup` ms of
    Just meta@Meta{..} | Hoping <- mstat -> case nattyEqEh k (vlen mctxt) of
      Just Refl -> flexEhWorker (mctxt, gamma, sig :^ th) mctxt sig (th ?^ gamma) th >>= \case
        Just (FlexEhWork ph ta) -> pure $ Just (FlexEh x k (ph -< th) ta)
        Nothing -> pure Nothing
      _ -> error "flexEh mismatch in meta arity"
    _ -> pure Nothing
flexEh _ _ _ = pure Nothing

constraintStatus :: Name -> Elab BOOL
constraintStatus name = normalise VN (atom STwo) (wrapMeta name)

ensureNull :: NATTY n => Context n -> Typ ^ n -> Norm Chk ^ n -> Elab BOOL
ensureNull ctx ty tm = case partitionEithers (listView tm) of
  ([], []) -> pure tRUE
  (_, _:_) -> pure fALSE
  (es, []) -> conjunction <$> (for es $ \ e -> do
      (_, stat) <- constrain "ensureNulls" $ Constraint
        { constraintCtx = fmap Hom <$> ctx
        , constraintType = Hom (mk SList ty)
        , lhs = E $^ e
        , rhs = nil
        }
      pure stat)

ensureCons :: NATTY n => Context n -> Typ ^ n -> Norm Chk ^ n -> Elab (Norm Chk ^ n, Norm Chk ^ n, BOOL)
ensureCons ctx ty tm = case listView tm of
  Right x:xs -> pure (x, unviewList ty xs, tRUE)
  _ -> do
    x <- invent "ensureHead" ctx ty
    xs <- invent "ensureTail" ctx (mk SList ty)
    (_, stat) <- constrain "ensureCons" $ Constraint
      { constraintCtx = fmap Hom <$> ctx
      , constraintType = Hom (mk SList ty)
      , lhs = tm
      , rhs = cons x xs
      }
    pure (x, xs, stat)

constrain :: String -> Constraint -> Elab (Name, BOOL)
constrain s c = do
  c <- updateConstraint c
  name <- metaDecl Hoping s emptyContext (atom STwo)
  solveConstraint name c
  (name,) <$> constraintStatus name

-- gets an updated dismounted frame, tries to solve it, remounts it
solveConstraint :: Name -> Constraint -> Elab ()
solveConstraint name c | debug ("Solve constrain call " ++ show name ++ " constraint = " ++ show c) False = undefined
solveConstraint name c@Constraint{..} = case (traverse (traverse isHom) constraintCtx, constraintType) of
  (Just ctx, Hom ty) -> nattily (vlen constraintCtx) $ do
    ms  <- gets metaStore
    lhsFlexEh <- flexEh ctx ty lhs
    rhsFlexEh <- flexEh ctx ty rhs
    case (lhs, rhs) of
      _ | lhs == rhs -> metaDefn name tRUE
      (_, t :^ ph)
        | Just (FlexEh x k th ta) <- lhsFlexEh
        , Just ps <- thicken ph th
        , x `Set.notMember` dependencies t -> do
              metaDefn x ((t :^ ps) //^ ta)
              metaDefn name tRUE
      (t :^ ph, _)
        | Just (FlexEh x k th ta) <- rhsFlexEh
        , Just ps <- thicken ph th
        , x `Set.notMember` dependencies t -> do
              metaDefn x ((t :^ ps) //^ ta)
              metaDefn name tRUE
      -- different atoms are never unifiable, raise the constraint as impossible
      _ | Just (s1, []) <- tagEh lhs
        , Just (s2, []) <- tagEh rhs
        , s1 /= s2 -> do
            debug ("Push Constraint n-5 " ++ show c) $ push $ ConstraintFrame name c
            debug (concat ["Unifying different atoms: ", s1, " and ", s2, "."]) $ metaDefn name fALSE
      _ | Just (SList, [elty])  <- tagEh ty
        , isUnitType elty -> elabTC ctx (natTermCancel (lhs,rhs)) >>= \case
            Left err -> error err
            Right (lhs', rhs') -> if Set.null (dependencies (tup [lhs', rhs']))
              then metaDefn name fALSE
              else if lhs == lhs'
                then push $ ConstraintFrame name c
                else do
                  (_, cstat) <- constrain "cancellation" $ Constraint
                    { constraintCtx = constraintCtx
                    , constraintType = Hom ty
                    , lhs = lhs'
                    , rhs = rhs'
                    }
                  metaDefn name cstat
      _ | Just (SList, [elty])  <- tagEh ty -> case mpullback (listView lhs) (listView rhs) of
            (frontEquals, (l1, l2)) -> case mpullback (reverse l1) (reverse l2) of
              (backEquals, (r1, r2)) -> case (reverse r1, reverse r2) of
                ([], []) -> metaDefn name tRUE
                (Right x:xs, Right y:ys) -> do
                  (_, hstat) <- constrain "listHeadEqual" $ Constraint
                    { constraintCtx = constraintCtx
                    , constraintType = Hom elty
                    , lhs = x
                    , rhs = y
                    }
                  (_, tstat) <- constrain "listTailEqual" $ Constraint
                    { constraintCtx = constraintCtx
                    , constraintType = Hom (mk SList elty)
                    , lhs = unviewList elty xs
                    , rhs = unviewList elty ys
                    }
                  metaDefn name (conjunction [hstat, tstat])
                _ | (Right x:xs, Right y:ys) <- (r1, r2) -> do
                  (_, hstat) <- constrain "listLastEqual" $ Constraint
                    { constraintCtx = constraintCtx
                    , constraintType = Hom elty
                    , lhs = x
                    , rhs = y
                    }
                  (_, tstat) <- constrain "listInitEqual" $ Constraint
                    { constraintCtx = constraintCtx
                    , constraintType = Hom (mk SList elty)
                    , lhs = unviewList elty (reverse xs)
                    , rhs = unviewList elty (reverse ys)
                    }
                  metaDefn name (conjunction [hstat, tstat])
                ([], l2) -> case partitionEithers l2 of
                  (_, _:_) -> metaDefn name fALSE
                  (es, []) | length frontEquals + length backEquals + length es > 1 -> ensureNull ctx elty (unviewList elty (map Left es)) >>= metaDefn name
                  _ -> push $ ConstraintFrame name Constraint{..}
                (l1, []) -> case partitionEithers l1 of
                  (_, _:_) -> metaDefn name fALSE
                  (es, []) | length frontEquals + length backEquals + length es > 1 -> ensureNull ctx elty (unviewList elty (map Left es)) >>= metaDefn name
                  _ -> push $ ConstraintFrame name Constraint{..}
                (l1, l2) -> do
                  let lhs = unviewList elty l1
                  let rhs = unviewList elty l2
                  push $ ConstraintFrame name Constraint{..}
      _ | Just (SAbel, [genTy]) <- tagEh ty -> do
          (_, stat) <- constrain "abel1" $ Abel1
            { constraintCtx = constraintCtx
            , genType = genTy
            , abelExp = mk Splus lhs (tup [lit (-1::Integer), rhs])
            }
          metaDefn name stat
      _ | Just (lt, ls) <- tagEh lhs
        , Just (rt, rs) <- tagEh rhs
        , lt == rt -> case (lt, ls, rs) of
          (tag, [lty], [rty]) | tag `elem` [SDest, SList, SAbel] -> do
            (_, stat) <- constrain "dest" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = constraintType
              , lhs = lty
              , rhs = rty
              }
            metaDefn name stat
          (SEnum, [ls], [rs]) -> do
            (_, stat) <- constrain "dest" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = ls
              , rhs = rs
              }
            metaDefn name stat
          (SQuantity, [lgenTy, ldim], [rgenTy, rdim]) -> do
             (_, gstat) <- constrain "genTy" $ Constraint
                  { constraintCtx = constraintCtx
                  , constraintType = Hom (atom SType)
                  , lhs = lgenTy
                  , rhs = rgenTy
                  }
             if alive gstat
               then do
                 (_, dstat) <- constrain "dim" $ Constraint
                   { constraintCtx = constraintCtx
                   , constraintType = mkConstraintType (mk SAbel lgenTy) gstat (mk SAbel rgenTy)
                   , lhs = ldim
                   , rhs = rdim
                   }
                 metaDefn name $ conjunction [gstat, dstat]
               else do
                 metaDefn name (I 0 :$ U :^ no Zy)
          (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs], [rowGenTy', colGenTy', cellTy', rs', cs'])
            | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy
            , Just (r', cellTy') <- lamNameEh cellTy', Just (c', cellTy') <- lamNameEh cellTy' -> do
                (_, rstat) <- constrain "rowTy" $ Constraint
                  { constraintCtx = constraintCtx
                  , constraintType = Hom (atom SType)
                  , lhs = rowGenTy
                  , rhs = rowGenTy'
                  }
                (_, cstat) <- constrain "colTy" $ Constraint
                  { constraintCtx = constraintCtx
                  , constraintType = Hom (atom SType)
                  , lhs = colGenTy
                  , rhs = colGenTy'
                  }
                if alive rstat && alive cstat
                  then do
                    let rowTy = mk SAbel rowGenTy
                    let rowTy' = mk SAbel rowGenTy'
                    let colTy = mk SAbel colGenTy
                    let colTy' = mk SAbel colGenTy'
                    (_, cellStat) <- constrain "cell" $ Constraint
                      { constraintCtx = constraintCtx
                                        \\\\ (r, mkConstraintType rowTy rstat rowTy')
                                        \\\\ (c, mkConstraintType (wk colTy) cstat (wk colTy'))
                      , constraintType = mkConstraintType (atom SType) (conjunction [rstat, cstat]) (atom SType)
                      , lhs = cellTy
                      , rhs = cellTy'
                      }
                    (_, rowStat) <- constrain "row" $ Constraint
                      { constraintCtx = constraintCtx
                      , constraintType = mkConstraintType (mk SList rowTy) rstat (mk SList rowTy')
                      , lhs = rs
                      , rhs = rs'
                      }
                    (_, colStat) <- constrain "col" $ Constraint
                      { constraintCtx = constraintCtx
                      , constraintType = mkConstraintType  (mk SList colTy) cstat (mk SList colTy')
                      , lhs = cs
                      , rhs = cs'
                      }
                    metaDefn name $ conjunction [rstat, cstat, cellStat, rowStat, colStat]
                  else
                    debug "RowTy/ColTy constraints - bad solution" $ metaDefn name (I 0 :$ U :^ no Zy)
          (Sone, [x], [y]) -> case tagEh ty of
            Just (tag, [elty]) | tag `elem` [SList, SAbel] -> do
              (_, cstat) <- constrain "singleton" $ Constraint
                { constraintCtx = constraintCtx
                , constraintType = Hom elty
                , lhs = x
                , rhs = y
                }
              metaDefn name cstat
            _ -> do
              debug ("Push Constraint n-6 " ++ show c) $ push $ ConstraintFrame name c
          _ -> do
            debug ("Push Constraint n-4 " ++ show c) $ push $ ConstraintFrame name c
      _ -> do
       debug ("Push Constraint n-3 " ++ show c) $ push $ ConstraintFrame name c
  _ -> do
    debug ("Push Constraint n-2 " ++ show c) $ push $ ConstraintFrame name c

solveConstraint name c@SubtypingConstraint{..} = let n = vlen constraintCtx in nattily n $ do
  let gotCtx = fmap lhsType <$> constraintCtx
  let wantCtx = fmap rhsType <$> constraintCtx
  if gotType == wantType then metaDefn name (I 1 :$ U :^ no Zy) else
    case tagEh gotType of
      Just (SAbel, [genTyGot]) -> do
        (genTyWant, aStat) <- ensureAbel wantCtx wantType
        stat <- subtype "subTypeAbelGot" genTyGot genTyWant
        metaDefn name (conjunction [aStat, stat])
      Just (tag, [elTyGot]) | tag `elem` [SList, SDest] -> do
        (elTyWant, dStat) <- ensureUTag tag wantCtx wantType
        stat <- subtype "subTypeUTagGot" elTyGot elTyWant
        metaDefn name (conjunction [dStat, stat])
      Just (SEnum, [genTyGot]) -> do
        (genTyWant, eStat) <- ensureEnum wantCtx wantType
        stat <- prefixConstraint constraintCtx genTyGot genTyWant
        metaDefn name (conjunction [eStat, stat])
      Just (SMatrix, [rowGenTyGot, colGenTyGot, cellTyGot, rsGot, csGot]) -> do
        (rowGenTyWant, colGenTyWant, cellTyWant, rsWant, csWant, mstat) <- ensureMatrix wantCtx wantType
        subMatrixType "submatrixGot" mstat (rowGenTyGot, colGenTyGot, cellTyGot, rsGot, csGot) (rowGenTyWant, colGenTyWant, cellTyWant, rsWant, csWant)
      Just (SQuantity, [genTyGot, dimGot]) -> do
        (genTyWant, dimWant, qStat) <- ensureQuantity wantCtx wantType
        stat <- subQuantityType "subQuantityGot" (genTyGot, dimGot) (genTyWant, dimWant)
        metaDefn name (conjunction [qStat, stat])
      Just (SPi, [srcGot, tgtGot]) -> do
        (srcWant, tgtWant, pStat) <- ensurePi wantCtx wantType
        stat <- subPiType "subPiGot" (srcGot, tgtGot) (srcWant, tgtWant)
        metaDefn name (conjunction [pStat, stat])
      Just (_, []) -> do
        (_ , stat) <- constrain "structuralEmptySubTypeGot" $ Constraint
          { constraintCtx = constraintCtx
          , constraintType = Hom (atom SType)
          , lhs = gotType
          , rhs = wantType
          }
        metaDefn name stat
      _ -> case tagEh wantType of
        Just (SAbel, [genTyWant]) -> do
          (genTyGot, aStat) <- ensureAbel gotCtx gotType
          stat <- subtype "subTypeAbelWant" genTyGot genTyWant
          metaDefn name (conjunction [aStat, stat])
        Just (tag, [elTyWant]) | tag `elem` [SList, SDest] -> do
          (elTyGot, dStat) <- ensureUTag tag gotCtx gotType
          stat <- subtype "subTypeUTagGot" elTyGot elTyWant
          metaDefn name (conjunction [dStat, stat])
        Just (SEnum, [genTyWant]) -> do
          (genTyGot, eStat) <- ensureEnum gotCtx gotType
          stat <- prefixConstraint constraintCtx genTyGot genTyWant
          metaDefn name (conjunction [eStat, stat])
        Just (SMatrix, [rowGenTyWant, colGenTyWant, cellTyWant, rsWant, csWant]) -> do
          (rowGenTyGot, colGenTyGot, cellTyGot, rsGot, csGot, mstat) <- ensureMatrix gotCtx gotType
          subMatrixType "submatrixWant" mstat (rowGenTyGot, colGenTyGot, cellTyGot, rsGot, csGot) (rowGenTyWant, colGenTyWant, cellTyWant, rsWant, csWant)
        Just (SQuantity, [genTyWant, dimWant]) -> do
          (genTyGot, dimGot, qStat) <- ensureQuantity gotCtx gotType
          stat <- subQuantityType "subQuantityWant" (genTyGot, dimGot) (genTyWant, dimWant)
          metaDefn name (conjunction [qStat, stat])
        Just (SPi, [srcWant, tgtWant]) -> do
          (srcGot, tgtGot, pStat) <- ensurePi gotCtx gotType
          stat <- subPiType "subPiWant" (srcGot, tgtGot) (srcWant, tgtWant)
          metaDefn name (conjunction [pStat, stat])
        Just (_, []) -> do
          (_ , stat) <- constrain "structuralEmptySubTypeWant" $ Constraint
            { constraintCtx = constraintCtx
            , constraintType = Hom (atom SType)
            , lhs = gotType
            , rhs = wantType
            }
          metaDefn name stat
        _ -> push $ ConstraintFrame name SubtypingConstraint{..}
 where
  prefixConstraint :: NATTY n => ConstraintContext n -> Term Chk ^ n -> Term Chk ^ n -> Elab BOOL
  prefixConstraint ctx Nil ws = pure $ tRUE
  prefixConstraint ctx gs Nil = do
    (_ , stat) <- constrain "enumPrefixNil" $ Constraint
      { constraintCtx = ctx
      , constraintType = Hom (mk SList (atom SAtom))
      , lhs = gs
      , rhs = nil
      }
    pure stat
  prefixConstraint ctx gs ws = do
    rs <- invent "rs" (fmap lhsType <$> ctx) (mk SList (atom SAtom))
    (_ , stat) <- constrain "enumPrefix" $ Constraint
      { constraintCtx = ctx
      , constraintType = Hom (mk SList (atom SAtom))
      , lhs = tag Splus [gs, rs]
      , rhs = ws
      }
    pure stat

  subtype s gotType wantType = snd <$> (constrain s $ SubtypingConstraint{..})

  subMatrixType s stat (rowGenTyGot, colGenTyGot, cellTyGot, rsGot, csGot) (rowGenTyWant, colGenTyWant, cellTyWant, rsWant, csWant)
    | Just (rGot, cellTyGot) <- lamNameEh cellTyGot, Just (cGot, cellTyGot) <- lamNameEh cellTyGot
    , Just (rWant, cellTyWant) <- lamNameEh cellTyWant, Just (cWant, cellTyWant) <- lamNameEh cellTyWant = let n = vlen constraintCtx in nattily n $ do
        let wantCtx = fmap rhsType <$> constraintCtx
        rstat <- subtype (s ++ "Row") rowGenTyGot rowGenTyWant
        cstat <- subtype (s ++ "Col") colGenTyGot colGenTyWant
        if alive rstat && alive cstat then do
          rowJoinElt <- invent "joinElementRow" wantCtx (mk SAbel rowGenTyWant)
          (_, headerRowStat) <- constrain (s ++ "HeaderCompatRow") $ HeadersCompatibility
            { constraintCtx = constraintCtx
            , leftGenType = rowGenTyGot
            , rightGenType = rowGenTyWant
            , joinGenType = rowGenTyWant
            , joinStatus = rstat
            , leftList = rsGot
            , rightList = rsWant
            , joinElement = rowJoinElt
            }
          colJoinElt <- invent "joinElementCol" wantCtx (mk SAbel colGenTyWant)
          (_, headerColStat) <- constrain (s ++ "HeaderCompatCol") $ HeadersCompatibility
            { constraintCtx = constraintCtx
            , leftGenType = colGenTyGot
            , rightGenType = colGenTyWant
            , joinGenType = colGenTyWant
            , joinStatus = cstat
            , leftList = csGot
            , rightList = csWant
            , joinElement = colJoinElt
            }
          (_, cellStat) <- constrain (s ++ "Cell") $ SubtypingConstraint
            { constraintCtx = constraintCtx \\\\ (rGot, Hom (mk SAbel rowGenTyGot)) \\\\ (cGot, Hom (wk $ mk SAbel colGenTyGot))
            , gotType = cellTyGot
            , wantType = cellTyWant //^ subSnoc (subSnoc (idSubst n :^ No (No (io n))) (R $^ (mk Splus (var 1) (wk (wk rowJoinElt)))  <&> wk (wk $ mk SAbel rowGenTyWant))) (R $^ (mk Splus (var 0) (wk (wk colJoinElt))) <&> wk (wk $ mk SAbel colGenTyWant))
            }
          metaDefn name $ conjunction [rstat, cstat, cellStat, headerRowStat, headerColStat]
        else
          metaDefn name (I 0 :$ U :^ no Zy)

  subPiType s (srcGot, tgtGot) (srcWant, tgtWant)
   | Just (tGot, tgtGot) <- lamNameEh tgtGot
   , Just (tWant, tgtWant) <- lamNameEh tgtWant = do
       srcStat <- subtype (s ++ "Src") srcWant srcGot
       (_, tgtStat) <- constrain (s ++ "Tgt") $ SubtypingConstraint
         { constraintCtx = constraintCtx \\\\ (tWant, Hom srcWant)
         , gotType = tgtGot
         , wantType = tgtWant
         }
       pure $ conjunction [srcStat, tgtStat]

  subQuantityType s (genTyGot, dimGot) (genTyWant, dimWant) = nattily (vlen constraintCtx) $ do
    gstat <- subtype (s ++ "GenTy") genTyGot genTyWant
    if alive gstat then do
      (_, dstat) <- constrain (s ++ "Dim") $ Constraint
        { constraintCtx = constraintCtx
        , constraintType = Hom (mk SAbel genTyWant)
        , lhs = dimGot
        , rhs = dimWant
        }
      pure $ conjunction [gstat, dstat]
    else pure (I 0 :$ U :^ no Zy)

solveConstraint name c@SameLength{..} = nattily (vlen constraintCtx) $ do
  let ((llefts, lrights), (rlefts, rrights)) =
        (partitionEithers $ listView leftList, partitionEithers $ listView rightList)
  let (ps, (lstuck, rstuck)) = mpullback (bag llefts) (bag rlefts)
  let (Sum sameLen, (Sum lextra, Sum rextra)) = mpullback (Sum $ length lrights) (Sum $ length rrights)
  let leftList' = (map Left $ sortBag lstuck) ++ map Right (drop sameLen lrights)
  let leftList = unviewList leftEltType leftList'
  let rightList' = (map Left $ sortBag rstuck) ++ map Right (drop sameLen rrights)
  let rightList = unviewList rightEltType rightList'
  case () of
    _ | null leftList' && null rightList' -> metaDefn name tRUE
    _ | bagSize lstuck + lextra == 0 && rextra > 0 -> metaDefn name fALSE
    _ | bagSize rstuck + rextra == 0 && lextra > 0 -> metaDefn name fALSE
    _ -> push $ ConstraintFrame name SameLength{..}

solveConstraint name InverseQuantities{..}
 | Just ctx <- traverse (traverse isHom) constraintCtx
 , Just (r, cellTy') <- lamNameEh cellTy, Just (c, cellTy'') <- lamNameEh cellTy'
 , Just (ic, invCellTy') <- lamNameEh invCellTy, Just (ir, invCellTy'') <- lamNameEh invCellTy'
  = let n = vlen constraintCtx in nattily n $ do
     let cellCtx = ctx \\\ (r, mk SAbel rowGenType) \\\ (c, wk $ mk SAbel colGenType)
     let invCtx = ctx \\\ (ic, mk SAbel colGenType) \\\ (ir, wk $ mk SAbel rowGenType)
     case [() | Just (SQuantity, _) <- map tagEh [cellTy'', invCellTy'']] of
       [] -> push $ ConstraintFrame name InverseQuantities{..}
       _ -> do
--         (genTy, dim, cstat) <- ensureQuantity cellCtx cellTy'
         (invGenTy, invDim, istat) <- ensureQuantity invCtx invCellTy''
         let sg = subSnoc (subSnoc (idSubst n :^ No (No (io n))) (var 0)) (var 1)
         (_ , tstat) <- constrain "quantityTypesEqual" $ Constraint
           { constraintCtx = fmap Hom <$> cellCtx
           , constraintType = Hom (atom SType)
           , lhs = cellTy''
           , rhs = mk SQuantity invGenTy (tup [lit (-1::Integer), invDim]) //^ sg
           }
         metaDefn name (conjunction [istat, tstat])

solveConstraint name c@Multiplicable{..}
 | Just ctx <- traverse (traverse isHom) constraintCtx = let n = vlen constraintCtx in nattily n $ do
     let (rowGenTy, leftMidGenTy, leftCellType) = leftTypes
     let (rightMidGenTy, colGenTy, rightCellType) = rightTypes
     let returnCtx = ctx \\\ ("i", mk SAbel rowGenTy) \\\ ("k", wk $ mk SAbel colGenTy)

     case awaitingStatus of
       Intg 0 -> metaDefn name (I 0 :$ U :^ no Zy)
       Intg 1 -> do
         case (tagEh leftCellType, tagEh rightCellType) of
           -- int * int case
           -- TODO: matching for `No No` does not account for metavariables
           (Just (SAbel, [x' :^ (No (No th))]), Just (SAbel, [y' :^ (No (No ph))])) -> do
             (_, xystat) <- constrain "xy" $ Constraint
               { constraintCtx = constraintCtx
               , constraintType = Hom (atom SType)
               , lhs = x' :^ th
               , rhs = y' :^ ph
               }
             (_, zstat) <- constrain "zx" $ Constraint
               { constraintCtx = fmap Hom <$> returnCtx
               , constraintType = Hom (atom SType)
               , lhs = returnCellType
               , rhs = leftCellType
               }
             metaDefn name (conjunction [xystat, zstat])
           (Just (SQuantity, [g0' :^ (No (No th)), d0]), Just (SQuantity, [g1' :^ (No (No ph)), d1])) -> do
             let g0 = g0' :^ th
             let g1 = g1' :^ ph
             (g, gstats) <- if g0 == g1 then pure (g0, []) else do
               g <- invent "generatorType" ctx (atom SType)
               (_, gstat) <- constrain "joinyThing" $ JoinConstraint
                 { constraintCtx = fmap Hom <$> ctx
                 , leftGenType = g0
                 , rightGenType = g1
                 , joinGenType = g
                 }
               pure (g, [gstat])
             d <- invent "answer" returnCtx (wk (wk (mk SAbel g)))
             (_ , retCellstat) <- constrain "returnCellTy" $ Constraint
               { constraintCtx = fmap Hom <$> returnCtx
               , constraintType = Hom (atom SType)
               , lhs = returnCellType
               , rhs = mk SQuantity (wk (wk g)) d
               }
             (_ , noMidDepStat) <- constrain "noMiddleDep" $ NoMiddleDependency
               { constraintCtx = fmap Hom <$> ctx
               , extension = (mk SAbel rowGenTy, mk SAbel joinGenType, mk SAbel colGenTy)
               , joinGenStatus = conjunction gstats
               , joinGenType = g
               , destination = d
               , candidate = mk Splus (wk d0)
                                      (d1 //^ subSnoc
                                                (subSnoc (idSubst n :^ No (No (No (io n))))
                                                         (R $^ tag Splus [E $^ var 1, wk (wk (wk joinElement))] <&> (wk (wk (wk $ mk SAbel joinGenType)))))
                                                (var 0))
               }
             metaDefn name (conjunction [retCellstat, noMidDepStat])
           _ -> push $ ConstraintFrame name Multiplicable{..}
       _ -> push $ ConstraintFrame name Multiplicable{..}

solveConstraint name c@JoinConstraint{..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = let n = vlen constraintCtx in nattily n $
      case (tagEh leftGenType, tagEh rightGenType, tagEh joinGenType) of
        _ | leftGenType == rightGenType -> do
          (_, stat) <- constrain "leftRightEqualJoin" $ Constraint
            { constraintCtx = constraintCtx
            , constraintType = Hom (atom SType)
            , lhs = leftGenType
            , rhs = joinGenType
            }
          metaDefn name stat
        (a, b, c) | not $ null [x | Just (SEnum, [x]) <- [a, b, c]] -> do
          (as, asStat) <- ensureEnum ctx leftGenType
          (bs, bsStat) <- ensureEnum ctx rightGenType
          (cs, csStat) <- ensureEnum ctx joinGenType
          (_ , pushStat) <- constrain "listpushout" $ ListAtomPushout
            { constraintCtx = constraintCtx
            , leftList = as
            , rightList = bs
            , joinList = cs
            }
          metaDefn name (conjunction [asStat, bsStat, csStat, pushStat])
        (a, b, c) | not $ null [() | Just (SMatrix, _) <- [a, b, c]] -> do
          (rowGenTyLeft, colGenTyLeft, cellTyLeft, rsLeft, csLeft, lstat) <- ensureMatrix ctx leftGenType
          (rowGenTyRight, colGenTyRight, cellTyRight, rsRight, csRight, rstat) <- ensureMatrix ctx rightGenType
          (rowGenTyJoin, colGenTyJoin, cellTyJoin, rsJoin, csJoin, jstat) <- ensureMatrix ctx joinGenType
          (i, j, cellTyLeft, cellTyRight, cellTyJoin) <- case () of
            _ | Just (i, cellTyLeft) <- lamNameEh cellTyLeft, Just (j, cellTyLeft) <- lamNameEh cellTyLeft
              , Just cellTyRight <- lamEh cellTyRight, Just cellTyRight <- lamEh cellTyRight
              , Just cellTyJoin <- lamEh cellTyJoin, Just cellTyJoin <- lamEh cellTyJoin
              -> pure (i, j, cellTyLeft, cellTyRight, cellTyJoin)
          (_, rowStat) <- constrain "plusJoinRows" $ JoinConstraint
            { constraintCtx = constraintCtx
            , leftGenType = rowGenTyLeft
            , rightGenType = rowGenTyRight
            , joinGenType = rowGenTyJoin
            }
          (_, colStat) <- constrain "plusJoinCols" $ JoinConstraint
            { constraintCtx = constraintCtx
            , leftGenType = colGenTyLeft
            , rightGenType = colGenTyRight
            , joinGenType = colGenTyJoin
            }
          if alive rowStat && alive colStat then do
            rowJoinElt <- invent "joinElementRow" ctx (mk SAbel rowGenTyJoin)
            (_, headerRowStat) <- constrain "HeaderCompatRow" $ HeadersCompatibility
              { constraintCtx = constraintCtx
              , leftGenType = rowGenTyLeft
              , rightGenType = rowGenTyRight
              , joinGenType = rowGenTyJoin
              , joinStatus = rowStat
              , leftList = rsLeft
              , rightList = rsRight
              , joinElement = rowJoinElt
              }
            colJoinElt <- invent "joinElementCol" ctx (mk SAbel colGenTyJoin)
            (_, headerColStat) <- constrain "HeaderCompatCol" $ HeadersCompatibility
              { constraintCtx = constraintCtx
              , leftGenType = colGenTyLeft
              , rightGenType = colGenTyRight
              , joinGenType = colGenTyJoin
              , joinStatus = colStat
              , leftList = csLeft
              , rightList = csRight
              , joinElement = colJoinElt
              }
            (_, rjStat) <- constrain "rowsOut" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (tag SAbel [rowGenTyJoin]))
              , lhs = rsLeft
              , rhs = rsJoin
              }
            (_, cjStat) <- constrain "rowsOut" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (tag SAbel [colGenTyJoin]))
              , lhs = csLeft
              , rhs = csJoin
              }
            (_, cellStat) <- constrain "Cell" $ JoinConstraint
              { constraintCtx = constraintCtx \\\\ (i, Hom (mk SAbel rowGenTyJoin)) \\\\ (j, Hom (wk $ mk SAbel colGenTyJoin))
              , leftGenType = cellTyLeft
              , rightGenType = cellTyRight //^ subSnoc (subSnoc (idSubst n :^ No (No (io n))) (R $^ (mk Splus (var 1) (wk (wk rowJoinElt)))  <&> wk (wk $ mk SAbel rowGenTyJoin))) (R $^ (mk Splus (var 0) (wk (wk colJoinElt))) <&> wk (wk $ mk SAbel colGenTyJoin))
              , joinGenType = cellTyJoin
              }
            metaDefn name $ conjunction [lstat,rstat,jstat,rowStat,colStat,headerRowStat,headerColStat,rjStat,cjStat,cellStat]
          else metaDefn name fALSE

        _ -> push $ ConstraintFrame name JoinConstraint{..}

solveConstraint name c@HeadersCompatibility{..} = nattily (vlen constraintCtx) $ do
      let leftCtx = fmap lhsType <$> constraintCtx
      let rightCtx = fmap rhsType <$> constraintCtx
      let consCase (leftElement , leftList) (rightElement, rightList) stat = do
            (_, hstat) <- constrain "headCompat" $ HeaderCompatibility{..}
            (_, tstat) <- constrain "tailCompat" $ HeadersCompatibility{..}
            metaDefn name (conjunction [tstat, hstat, stat])
      case listView leftList of
        [] -> ensureNull rightCtx (mk SAbel rightGenType) rightList >>= metaDefn name
        Right x:xs -> do
          (y, ys, stat) <- ensureCons rightCtx (mk SAbel rightGenType) rightList
          consCase (x , unviewList (mk SAbel leftGenType) xs) (y, ys) stat
        _ -> case listView rightList of
          [] -> ensureNull leftCtx (mk SAbel leftGenType) leftList >>= metaDefn name
          Right y:ys -> do
            (x, xs, stat) <- ensureCons leftCtx (mk SAbel leftGenType) leftList
            consCase (x , xs) (y, unviewList (mk SAbel rightGenType) ys) stat
          _ -> push $ ConstraintFrame name HeadersCompatibility{..}

solveConstraint name HeaderCompatibility{..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = nattily (vlen constraintCtx) $ do
      case joinStatus of
        Intg 0 -> metaDefn name fALSE
        Intg 1 -> do
          (_, hstat) <- constrain "headerCompat" $ Constraint
            { constraintCtx = constraintCtx
            , constraintType = Hom (mk SAbel joinGenType)
            , lhs = joinElement
            , rhs = mk Splus (negTm leftElement) rightElement
            }
          metaDefn name hstat
        _ -> push $ ConstraintFrame name HeaderCompatibility{..}

        {-
        (LIsCons (x, xs), ) -> do
          hstats <- case tagEh joinType of
            Just (SAbel, [_]) -> do
              pure [hstat]
            _ -> do  -- TODO: check if this really makes sense, sometime
              (_, hstat) <- constrain "headEqual" $ Constraint
                { constraintCtx = constraintCtx
                , constraintType = Het leftType joinStatus rightType
                , lhs = x
                , rhs = y
                }
              pure [hstat]
          (_, tstat) <- constrain "tailCompat" $ HeaderCompatibility
            { leftList = xs
            , rightList = ys
            , ..
            }
          metaDefn name (conjunction (tstat : hstats))
        _ ->
-}

solveConstraint name c@NoMiddleDependency{ candidate = candidate@(cand' :^ th), ..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = nattily (vlen constraintCtx) $ do
  case joinGenStatus of
    Intg 0 -> metaDefn name (I 0 :$ U :^ no Zy)
    Intg 1 -> do
      let (i, j, k) = extension
      -- TODO: this will say no incorrectly when the only occurrence of j is as a permitted dependency of a meta variable; the right thing to do is to prune this dependency
      case (case th of { Su (No th) -> Just (Su th) ; No (No th) -> Just (No th) ; _ -> Nothing}) of
        Just th -> do
          (_ , stat) <- constrain "" $ Constraint
            { constraintCtx = fmap Hom <$> (ctx \\\ ("i", i) \\\ ("k", wk k))
            , constraintType = Hom (mk SAbel (wk (wk joinGenType)))
            , lhs = destination
            , rhs = cand' :^ th
            }
          metaDefn name stat
        Nothing -> push $ ConstraintFrame name NoMiddleDependency{..}
    _ -> push $ ConstraintFrame name NoMiddleDependency{..}

solveConstraint name c@ElemConstraint{..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = do
      let (as, Any b) = knownElems hayStack
      if needle `elem` as
        then metaDefn name (I 1 :$ U :^ no Zy)
        else if b then push $ ConstraintFrame name c else metaDefn name (I 0 :$ U :^ no Zy)
  where
    knownElems :: Term Chk ^ n -> ([String], Any)
    knownElems t | Just ("", []) <- tagEh t = ([], Any False)
    knownElems t | Just (Splus, [x, y]) <- tagEh t = knownElems x <> knownElems y
                 | Just (Sone, [a]) <- tagEh t = case a of
                     A s :$ _ :^ _ -> ([s], Any False)
                     a -> ([], Any $ not (Set.null (dependencies a))) -- TODO: over approximation; will sometimes say maybe when it should say no
    knownElems t = ([], Any $ not (Set.null (dependencies t))) -- TODO: over approximation; will sometimes say maybe when it should say no
solveConstraint name c@ListAtomPushout{..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = nattily (vlen constraintCtx) $ do
      case (listView leftList, listView rightList, listView joinList) of
        _ | leftList == rightList -> do
              (_ , jStat) <- constrain "equalInputs" $ Constraint
                { constraintCtx = constraintCtx
                , constraintType = Hom (mk SList (atom SAtom))
                , lhs = joinList
                , rhs = leftList
                }
              metaDefn name jStat
        ([], _, _) -> do
            (_ , jStat) <- constrain "leftEmpty" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = joinList
              , rhs = rightList
              }
            metaDefn name jStat
        (_ , [], _) -> do
            (_ , jStat) <- constrain "rightEmpty" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = joinList
              , rhs = leftList
              }
            metaDefn name jStat
        (_ , _, []) -> do
            (_ , lStat) <- constrain "leftEmptyJ" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = leftList
              , rhs = nil
              }
            (_ , rStat) <- constrain "rightEmptyJ" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = rightList
              , rhs = nil
              }
            metaDefn name (conjunction [lStat, rStat])
        (Right x:xs, Right y:ys, _) -> do
            (_ , headStat) <- constrain "headEqual" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (atom SAtom)
              , lhs = x
              , rhs = y
              }
            joinTail <- invent "joinTail" ctx (mk SList (atom SAtom))
            (_ , tailStat) <- constrain "tailConstraint" $ ListAtomPushout
              { constraintCtx = constraintCtx
              , leftList = unviewList (atom SAtom) xs
              , rightList = unviewList (atom SAtom) ys
              , joinList = joinTail
              }
            (_ , resStat) <- constrain "resJoinList" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom (mk SList (atom SAtom))
              , lhs = joinList
              , rhs = tag Splus [tag Sone [x], joinTail]
              }
            metaDefn name (conjunction [headStat, tailStat, resStat])
        _ -> push $ ConstraintFrame name ListAtomPushout{..}

solveConstraint name c@Abel1{..} = case abelView abelExp of
  NFAbel{nfConst = 0, nfStuck = []} -> metaDefn name tRUE
  NFAbel{nfConst = _, nfStuck = []} -> metaDefn name fALSE
  NFAbel{..} -> do
    if Set.null (foldMap (dependencies . fst) nfStuck)
      then metaDefn name fALSE
      else push $ ConstraintFrame name Abel1{..}

solveConstraint name c = debug ("Push Constraint n " ++ show c) $ push $ ConstraintFrame name c

constrainEqualType :: TYPE -> TYPE -> Elab (Name, BOOL)
constrainEqualType lhs rhs = constrain "Q" $ Constraint
  { constraintCtx   = VN
  , constraintType  = Hom (atom SType)
  , lhs = lhs
  , rhs = rhs
  }

findDeclaration :: DeclarationType (Maybe TYPE) -> Elab (Maybe (Name, TYPE))
findDeclaration UserDecl{varTy = ty, currentName = old, seen, newNames = news, whereAmI = whereTo} = excursion (go False)
  where
  go :: Bool {- we think we are in a function -} -> Elab (Maybe (Name, TYPE))
  go b = pull >>= \case
    Nothing -> pure Nothing
    Just f -> case f of
      Locale ScriptLocale | b -> -- if we are in a function, script
        Nothing <$ push f        -- variables are out of scope
      Locale (FunctionLocale _) -> shup f >> go True -- we know we are in a function
      Declaration n u'@UserDecl{varTy = ty', currentName = old', seen = seen', newNames = news', whereAmI = whereFrom}
        | old == old'
        , whereFrom <= whereTo -> do
        case ty of
          Just ty -> () <$ constrainEqualType ty ty'
          Nothing -> pure ()
        Just (n, ty') <$ push (Declaration n u'{seen = seen' || seen, newNames = news' ++ news})
      _ -> shup f >> go b

makeDeclaration :: DeclarationType TYPE -> Elab (Name, TYPE)
makeDeclaration d@UserDecl{varTy, currentName, whereAmI} = excursion $ do
  findLocale
  let xty = case whereAmI of
        LabMate -> varTy
        MatLab  -> mk SDest varTy
  x <- metaDecl ProgramVar currentName emptyContext xty
  (x, varTy) <$ push (Declaration x d)
  where
    findLocale = pull >>= \case
      Nothing -> error "Locale disappeared!"
      Just f  -> shup f >> case f of
        Locale{} -> pure ()
        _ -> findLocale

freshDeclaration :: DeclarationType TYPE -> Elab (Maybe (Name, TYPE))
freshDeclaration d = findDeclaration (fmap Just d) >>= \case
  Just _ -> pure Nothing
  Nothing -> Just <$> makeDeclaration d

ensureDeclaration :: DeclarationType (Maybe TYPE) -> Elab (Name, TYPE)
ensureDeclaration s = findDeclaration s >>= \case
  Nothing -> ensureType s >>= makeDeclaration
  Just x  -> pure x

onNearestSource :: ([Tok] -> [Tok]) -> Elab ()
onNearestSource f = excursion go where
  go = pull >>= \case
    Nothing -> error "Impossible: no enclosing Source frame"
    Just (Source (n, Hide ts)) -> pushSource (n, Hide $ f ts)
    Just f -> shup f >> go

pushDefinition :: Name -> TERM -> Elab ()
pushDefinition name def = excursion go where
  go = pull >>= \case
    Nothing -> error "LabMate: Do not make definitions for undeclared variables"
    Just fr@(Declaration n _) | n == name -> traverse_ push [fr, Definition name def]
    Just fr -> shup fr >> go

metaDecl :: Status -> String -> Context n -> Typ ^ n -> Elab Name
metaDecl s x ctx ty = do
   x <- fresh x
   x <$ modifyNearestStore (Map.insert x (Meta ctx ty Nothing s))

metaDeclTerm :: Status -> String -> Context n -> Typ ^ n -> Elab (Term Chk ^ n)
metaDeclTerm s x ctx ty = nattily (vlen ctx) (wrapMeta <$> metaDecl s x ctx ty)

metaDefn :: Name -> Term Chk ^ n -> Elab ()
metaDefn x def = getMeta x >>= \case
  Meta{..}
    | Just Refl <- scopeOf def `nattyEqEh` vlen mctxt
    , mstat `elem` [Waiting, Hoping] -> nattily (scopeOf def) $ do
      tick
      debug (concat ["Meta Defn ", show x, " := ", show def]) $
        modifyNearestStore (Map.insert x (Meta mctxt mtype (Just def) mstat))
  Meta{..} -> error . concat $
    ["metaDefn: check the status or the scope of ", nattily (scopeOf def) $ show def
    , " in scope ", show (scopeOf def)
    , " for " , show x
    , " in meta scope ", show (vlen mctxt)]

invent' :: Status -> String -> Context n -> Typ ^ n -> Elab (Term Chk ^ n)
invent' stat x ctx ty = nattily (vlen ctx) $ normalise ctx (atom SType) ty >>= \case
  ty
    | isUnitType ty -> pure nil
    | Just (SPi, [s, t]) <- tagEh ty, Just (y, t) <- lamNameEh t ->
      lam y <$> invent x (ctx \\\ (y, s)) t
    | Just (SSig, [s, t]) <- tagEh ty, Just (y, t) <- lamNameEh t -> do
        a <- invent x ctx s
        d <- invent x ctx (t //^ sub0 (R $^ a <&> s))
        pure (T $^ a <&> d)
  ty -> wrapMeta <$> metaDecl stat x ctx ty

invent :: String -> Context n -> Typ ^ n -> Elab (Term Chk ^ n)
invent = invent' Hoping

ensureType :: DeclarationType (Maybe TYPE) -> Elab (DeclarationType TYPE)
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
    pushProblems (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move winning
  LHS (LVar x) -> do
    (x, _) <- ensureDeclaration (UserDecl Nothing x True [] True MatLab)
    newProb . Done $ FreeVar x
    move winning
  LHS (LMat []) -> do
    newProb $ Done nil
    move winning
  FormalParam x -> do
    ty <- invent (x ++ "Type") emptyContext (atom SType)
    val <- invent' Abstract (x ++ "Val") emptyContext ty
    (x, _) <- makeDeclaration (UserDecl ty x True [] False MatLab)
    -- TODO: should this be `postLeft`?
    excursion $ postRight [Currently ty (FreeVar x) val]
    newProb . Done $ FreeVar x
    move winning
  Expression (Var x) ->
    findDeclaration (UserDecl Nothing x True [] False MatLab) >>= \case
    Nothing -> do
      newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
      move Whacked
    Just (x, _) -> do
      newProb . Done $ FreeVar x
      move winning
  Expression (App (f :<=: src) args) -> do
    pushProblems $ Sourced . fmap Expression <$> args
    pushSource src
    newProb $ FunCalled f
    run
  Expression (Brp (e :<=: src) args) -> do
    pushProblems $ Sourced . fmap Expression <$> args
    pushSource src
    newProb $ Expression e
    run
  Expression (Dot (e :<=: src) fld) -> do
    pushSource src
    newProb $ Expression e
    run
  Expression (Mat es) -> do
    pushProblems (Row <$> es)
    newProb $ Done nil
    move winning
  Expression (IntLiteral i) -> newProb (Done $ lit i) >> move winning
  Expression (DoubleLiteral d) -> newProb (Done $ lit d) >> move winning
  Expression (StringLiteral s) -> newProb (Done $ lit s) >> move winning
  Expression (UnaryOp op (e :<=: src)) -> do
    pushSource src
    newProb $ Expression e
    run
  Expression (BinaryOp op (e0 :<=: src0) e1) -> do
    pushProblems [Sourced (Expression <$> e1)]
    pushSource src0
    newProb $ Expression e0
    run
  Expression ColonAlone -> newProb (Done $ atom ":") >> move winning
  Expression (Handle f) -> newProb (Done $ T $^ atom "handle" <&> atom f) >> move winning
  FunCalled f -> newProb (Expression f) >> run
  Row rs -> case rs of
    [] -> newProb (Done nil) >> move winning
    (r :<=: src):rs -> do
      pushProblems (Sourced . fmap Expression <$> rs)
      pushSource src
      newProb $ Expression r
      run
  Command (Assign lhs rhs) -> do
    synthMode <- case lhs of
      LVar x :<=: _ -> do
        m <- findDeclaration $
          UserDecl{ varTy = Nothing
                  , currentName = x
                  , seen = True
                  , newNames = []
                  , capturable = True
                  , whereAmI = MatLab}
        case m of
          Nothing -> pure FindSimplest
          Just _ -> pure EnsureCompatibility
      _ -> pure FindSimplest
    -- TODO: optimise for the case when we know the LHS type
    ty <- invent "assignTy" emptyContext (atom SType)
    (ltm, lhsProb) <- elab "AssignLHS" emptyContext (mk SDest ty) (LHSTask <$> lhs)
    (rtm, rhsProb) <- elab "AssignRHS" emptyContext ty (ExprTask MatLab synthMode <$> rhs)
    excursion $ postRight [Currently ty ltm rtm]
    pushProblems [rhsProb]
    newProb lhsProb
    run
  Command (Direct rl (dir :<=: src)) -> do
    pushSource src
    runDirective rl dir
  Command (Function (lhs, fname :<=: _, args) cs) ->
    findDeclaration (UserDecl Nothing fname True [] False MatLab)  >>= \case
      Nothing -> error "function should have been declared already"
      Just (fname, _) -> do
        traverse_ fundecl cs
        traverse_ push [ Locale (FunctionLocale fname)
                       , Fork (Left MkFork{fprob = Sourced (LHS <$> lhs), fframes = [], fstatus = worried})
                       ]
        pushProblems $ (Sourced . fmap FormalParam <$> args) ++ (Sourced . fmap Command <$> cs)
        newProb $ Done nil
        move winning
  Command (Respond ts) -> do
    onNearestSource $ const []
    newProb $ Done nil
    move winning
  Command (GeneratedCode cs) -> do
    onNearestSource $ const []
    newProb $ Done nil
    move winning
  Command (If brs els) -> do
    let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els
    pushProblems $ conds >>= \(e, cs) -> Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move winning
  Command (For (x, e :<=: src) cs) -> do
    pushProblems $ (Sourced. fmap Command <$> cs) ++ [Sourced (LHS . LVar <$> x)]
    pushSource src
    newProb $ Expression e
    run
  Command (While e cs) -> do
    pushProblems $ Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Done nil
    move winning
  Command Break -> newProb (Done nil) >> move winning
  Command Continue -> newProb (Done nil) >> move winning
  Command Return -> newProb (Done nil) >> move winning
  Command (Switch exp brs els) -> do
    let conds = brs ++ foldMap (\cs -> [(noSource $ IntLiteral 1, cs)]) els -- TODO: handle `otherwise` responsibly
    pushProblems $ conds >>= \(e, cs) ->  Sourced (Expression <$> e) : (Sourced . fmap Command <$> cs)
    newProb $ Sourced (Expression <$> exp)
    run
  RenameAction old new rl -> do
    ensureDeclaration $
      UserDecl{ varTy = Nothing
              , currentName = old
              , seen = False
              , newNames = [(new, rl)]
              , capturable = True
              , whereAmI = MatLab }
    newProb $ Done nil
    move winning
  DeclareAction ty name -> do
    (name, _) <- ensureDeclaration $
      UserDecl{ varTy = Just ty
              , currentName = name
              , seen = False
              , newNames = []
              , capturable = True
              , whereAmI = MatLab}
    newProb $ Done (FreeVar name)
    move winning
  InputFormatAction name body (n, c) -> do
    modify $ \st@MS{..} -> st { nonceTable = Map.insertWith (++) n (concat["\n", replicate c ' ', "%<{", "\n", generateInputReader name body, "\n", replicate c ' ', "%<}"]) nonceTable }
    newProb $ Done nil
    move winning
  Elab name etask -> do
    meta <- getMeta name
    runElabTask name meta etask
  Prefer p1 p2 -> debugCatch "Prefer" $ do
    push . Catch $ MkFork worried [] p2
    push $ LocalStore mempty
    newProb p1
    run
  Whack -> debugCatch "Whack whack" $ do
    move Whacked
  Worry -> debugCatch "Worry worry" $ do
    move worried
  Sourced (p :<=: src) -> do
    localNamespace . take 10 . filter isAlpha $ show p
    pushSource src
    newProb p
    run
  Problems [] -> do
    newProb $ Done nil
    move winning
  Problems (p : ps) -> do
    pushProblems ps
    newProb p
    run
  Done _ -> move winning
  p -> trace ("Falling through. Problem = " ++ show p) $ move worried
 -- _ -> move worried

runDirective :: ResponseLocation -> Dir' -> Elab ()
runDirective rl (dir :<=: src, body) = do
  pushSource src
  case dir of
    Rename old new -> do
      newProb $ RenameAction old new rl
      run
    InputFormat name | Just (InputFormatBody body) <- body -> do
      newProb $ InputFormatAction name body rl
      run
    ReadFrom filename variables -> do
      vs <- for variables $ \ v -> findDeclaration (UserDecl{varTy = Nothing, currentName = v, seen = False, newNames = [], capturable = False, whereAmI = MatLab}) >>= \case
        Just (name, ty) -> do
          pushDefinition name (E $^ M (name, Zy) $^ S0 $^ U :^ Ze)
          pure $ Right (v, ty)
        Nothing -> pure $ Left $ "Unknown variable " ++ v
      push $ Diagnostic rl (ReadFromD filename vs)
      newProb $ Done nil
      run
    Declare xs ty -> do
      (sol, prob) <- elab "declType" emptyContext (atom SType) (TensorTask <$> ty)
      pushProblems (Sourced . fmap (DeclareAction sol) <$> xs)
      newProb prob
      run
    Typecheck ty e -> do
      (tySol, tyProb) <- elab "typeToCheck" emptyContext (atom SType) (TensorTask <$> ty)
      (eSol, eProb) <- elab "exprToCheck" emptyContext tySol (ExprTask LabMate EnsureCompatibility <$> e)
      newProb tyProb
      run
    SynthType e -> do
      ty <- invent "typeToSynth" emptyContext (atom SType)
      (eSol, eProb) <- elab "exprToSynth" emptyContext ty (ExprTask LabMate FindSimplest <$> e)
      push $ Diagnostic rl (SynthD ty eSol e)
      newProb eProb
      run
    Dimensions (g :<=: gsrc) (q :<=: qsrc) unitAtoms -> do
      let generators = mk SEnum $ foldr (mk Splus . (mk Sone :: TERM -> TERM) . atom . what) nil (snd <$> unitAtoms) :: TYPE
      generators <- normalise emptyContext (atom SType) generators
      let gdef = mk SAbel generators :: TYPE
      let gdecl = UserDecl
            { varTy = mk SType
            , currentName = g
            , seen = False
            , newNames = []
            , capturable = False
            , whereAmI = LabMate
            }
      freshDeclaration gdecl >>= \case
        Nothing -> move worried
        Just (g, gty) -> do
          pushDefinition g gdef
          let qdecl = UserDecl
                { varTy = mk SPi gdef (lam "_" (mk SType))
                , currentName = q
                , seen = False
                , newNames = []
                , capturable = False
                , whereAmI = LabMate
                }
          freshDeclaration qdecl >>= \case
            Nothing -> move worried
            Just (q', qty) -> do
              pushDefinition q' (lam "d" $ mk SQuantity (wk generators) (evar 0))
              ps <- fmap concat . for (zip [0..] unitAtoms) $ \case
                (_, (Nothing, _)) -> pure []
                (i, (Just u, _)) -> do
                  let uty = singMatTy (mk SQuantity generators (tag Sone [lit (i :: Integer)]))
                  (ltm, lhsProb) <- elab "unitFakeLHS" emptyContext (mk SDest uty) (LHSTask . LVar <$> u)
                  excursion $ postRight [Currently uty ltm (mk Sone (lit (1::Double)))]
                  pure [(lhsProb, u)]
              modify $ \st@MS{..} -> st{refoldingMap = Map.insert generators q refoldingMap}
              unless (null ps) $ do
                push . Diagnostic rl $ UnitDs (snd <$> ps)
                pushProblems (fst <$> ps)
              newProb $ Done nil
              run
    Unit u ty -> do
      _ <- debug "Elaborating unit decl" $ pure True

      genTy <- invent "genTy" VN (atom SType)
      let abelTy = mk SAbel genTy :: TYPE
      dim <- invent "dimension" VN abelTy
      let qty = mk SQuantity genTy dim :: TYPE
      let mty = singMatTy qty
      -- let cellTy = mk SQuantity (wk (wk genTy)) (tag Splus [wk (wk dim), tag Splus [evar 0, tup [lit (-1 :: Int), evar 1]]]) :: Term Chk ^ S (S Z)
      -- let mty = mk SMatrix abelTy abelTy (lam "i" $ lam "j" $ cellTy) (tag Sone [nil]) (tag Sone [nil])
      _ <- debug "Constructing Unit type " $ pure True
      (ltm, lhsProb) <- elab "unitFakeLHS" emptyContext (mk SDest mty) (LHSTask . LVar <$> u)
      (tySol, tyProb) <- elab "unitType" emptyContext (atom SType) (TypeExprTask LabMate EnsureCompatibility <$> ty)
      excursion $ postRight [Currently mty ltm (mk Sone (lit (1::Double)))]
      (_, stat) <- constrain "unitType" $ Constraint
              { constraintCtx = VN
              , constraintType = Hom (atom SType)
              , lhs = qty
              , rhs = tySol
              }
      push $ Diagnostic rl (UnitD (nonce u) stat (nonce ty))
      pushProblems [tyProb, lhsProb]
      newProb $ Done nil
      run
    _ -> move worried

elab'
  :: String -- name advice for new elaboration prob
  -> Context n
  -> Typ ^ n -- the type of the solution
  -> ElabTask
  -> Elab (Term Chk ^ n, Problem)
elab' x ctx ty etask = nattily (vlen ctx) $ do
  x <- metaDecl Waiting x ctx ty
  pure (wrapMeta x, Elab x etask)

elab
  :: String -- name advice for new elaboration prob
  -> Context n
  -> Typ ^ n -- the type of the solution
  -> WithSource ElabTask
  -> Elab (Term Chk ^ n, Problem)
elab x ctx ty (etask :<=: src) =
  fmap (Sourced . (:<=: src)) <$> elab' x ctx ty etask


ensureMatrix :: Context n -> NmTy ^ n -> Elab (NmTy ^ n, NmTy ^ n, NmTy ^ n, Norm Chk ^ n, Norm Chk ^ n, BOOL)
ensureMatrix ctxt ty
  | Just (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs]) <- tagEh ty
  {- , Just cellTy <- lamEh cellTy
  , Just cellTy <- lamEh cellTy -} = pure (rowGenTy, colGenTy, cellTy, rs, cs, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
      rowGenTy <- invent "rowType" ctxt (atom SType)
      colGenTy <- invent "colType" ctxt (atom SType)
      let ctxtRC = ctxt \\\ ("r", mk SAbel rowGenTy) \\\ ("c", wk $ mk SAbel colGenTy)
      cellTy <- lam "r" . lam "c" <$> invent "cellType" ctxtRC (atom SType)
      rs <- invent "rs" ctxt (mk SList (tag SAbel [rowGenTy]))
      cs <- invent "cs" ctxt (mk SList (tag SAbel [colGenTy]))
      (_, cstat) <- constrain "ensureMat" $ Constraint
        { constraintCtx = fmap Hom <$> ctxt
        , constraintType = Hom (atom SType)
        , lhs = mk SMatrix rowGenTy colGenTy cellTy rs cs
        , rhs = ty
        }
      pure (rowGenTy, colGenTy, cellTy, rs, cs, cstat)

unpackCellType :: Term Chk ^ n -> ((String, String), Term Chk ^ S (S n))
unpackCellType tm
  | Just (r, tm) <- lamNameEh tm, Just (c, tm) <- lamNameEh tm = ((r, c), tm)
  | otherwise = error "unpackCellType: malformed cell type"

ensureUTag :: String -> Context n -> NmTy ^ n -> Elab (Norm Chk ^ n, BOOL)
ensureUTag tag ctxt ty | Just (tag, [t]) <- tagEh ty = pure (t, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
     t <- invent "tagElTy" ctxt (atom SType)
     (_ , tStat) <- constrain "tagTy" $ Constraint
       { constraintCtx = fmap Hom <$> ctxt
       , constraintType = Hom (atom SType)
       , lhs = ty
       , rhs = mk tag t
       }
     pure (t, tStat)

ensureEnum :: Context n -> NmTy ^ n -> Elab (Norm Chk ^ n, BOOL)
ensureEnum ctxt ty | Just (SEnum, [xs]) <- tagEh ty = pure (xs, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
     as <- invent "atoms" ctxt (mk SList (atom SAtom))
     (_ , asStat) <- constrain "enumAtoms" $ Constraint
       { constraintCtx = fmap Hom <$> ctxt
       , constraintType = Hom (atom SType)
       , lhs = ty
       , rhs = mk SEnum as
       }
     pure (as, asStat)

ensureAbel :: Context n -> NmTy ^ n -> Elab (NmTy ^ n, BOOL)
ensureAbel ctxt ty | Just (SAbel, [g]) <- tagEh ty = pure (g, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
     g <- invent "genTy" ctxt (atom SType)
     (_ , gStat) <- constrain "abelG" $ Constraint
       { constraintCtx = fmap Hom <$> ctxt
       , constraintType = Hom (atom SType)
       , lhs = ty
       , rhs = mk SAbel g
       }
     pure (g, gStat)

ensurePi :: Context n -> NmTy ^ n -> Elab (NmTy ^ n, NmTy ^ n, BOOL)
ensurePi ctxt ty | Just (SPi, [src, tgt]) <- tagEh ty = pure (src, tgt, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
     src <- invent "srcTy" ctxt (atom SType)
     tgt <- invent "tgtTy" (ctxt \\\ ("x", src)) (atom SType)
     let ltgt = lam "x" tgt
     (_ , pStat) <- constrain "pi" $ Constraint
       { constraintCtx = fmap Hom <$> ctxt
       , constraintType = Hom (atom SType)
       , lhs = ty
       , rhs = mk SPi src ltgt
       }
     pure (src, ltgt, pStat)

ensureQuantity :: Context n -> NmTy ^ n -> Elab (NmTy ^ n, Norm Chk ^ n, BOOL)
ensureQuantity ctxt ty | Just (SQuantity, [genTy, dim]) <- tagEh ty = pure (genTy, dim, tRUE)
  | otherwise = nattily (vlen ctxt) $ do
     genTy <- invent "genTy" ctxt (atom SType)
     dim <- invent "dim" ctxt (mk SAbel genTy)
     (_ , qStat) <- constrain "quantity" $ Constraint
       { constraintCtx = fmap Hom <$> ctxt
       , constraintType = Hom (atom SType)
       , lhs = ty
       , rhs = mk SQuantity genTy dim
       }
     pure (genTy, dim, qStat)


doubleType :: Term Chk ^ Z
doubleType =  mk SQuantity (tag SEnum [nil]) nil

runElabTask
  :: Name
  -> Meta     -- meta which carries the solution for T
  -> ElabTask -- T
  -> Elab ()
runElabTask _ meta task | debug (concat ["Elaborating ", show meta, " for task ", show task]) False  = undefined
runElabTask sol meta@Meta{..} etask = nattily (vlen mctxt) $ do
  mtype <- normalise mctxt (atom SType) mtype
  case etask of
    TensorTask (Tensor ((x, xs :<=: xSrc), (y, ys :<=: ySrc)) (eTy :<=: eSrc)) -> do
      xGenTy <- invent (x ++ "GenType") mctxt (atom SType)
      yGenTy <- invent (y ++ "GenType") mctxt (atom SType)
      let xTy = mk SAbel xGenTy
      let yTy = mk SAbel yGenTy
      (xsSol, xsProb) <- elab (x ++ "List") mctxt (mk SList xTy) (TypeExprTask LabMate EnsureCompatibility xs :<=: xSrc)
      (ysSol, ysProb) <- elab (y ++ "List") mctxt (mk SList yTy) (TypeExprTask LabMate EnsureCompatibility ys :<=: ySrc)
      let ctx = mctxt \\\ (x, xTy) \\\ (y, wk yTy)
      (eSol, eProb) <- elab "entryType" ctx (atom SType) (TypeExprTask LabMate EnsureCompatibility eTy :<=: eSrc)
      pushProblems [xsProb, ysProb, eProb]
      metaDefn sol (mk SMatrix xGenTy yGenTy (lam x . lam y $ eSol) xsSol ysSol)
      newProb $ Done nil
      move winning
    TypeExprTask LabMate _ (TyVar Ldouble) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ doubleType -< no (vlen mctxt)
      newProb $ Done nil
      move winning
    TypeExprTask LabMate _ (TyVar Lint) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SAbel oneType -< no (vlen mctxt)
      newProb $ Done nil
      move winning
    TypeExprTask LabMate _ (TyVar Lstring) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SList (atom SChar) -< no (vlen mctxt)
      newProb $ Done nil
      move winning
    TypeExprTask whereAmI synthMode (TyVar x)
      | Just (xtm, xty) <- lookupInContext x mctxt -> do
        (_, xstat) <- constrain "VarExprCtxt" $ case synthMode of
            FindSimplest ->
              Constraint
              { constraintCtx = fmap Hom <$> mctxt
              , constraintType = Hom (atom SType)
              , lhs = xty
              , rhs = mtype
              }
            EnsureCompatibility ->
              SubtypingConstraint
              { constraintCtx = fmap Hom <$> mctxt
              , gotType = xty
              , wantType = mtype
              }
        pushProblems [Elab sol $ Await xstat xtm]
        newProb $ Done nil
        run
      | otherwise -> findDeclaration (UserDecl Nothing x True [] False whereAmI) >>= \case
        Nothing -> do
          newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
          cry sol
          move Whacked
        Just (x, xty) -> do
          (_, xstat) <- constrain "VarExpr" $ case synthMode of
              FindSimplest ->
                Constraint
                { constraintCtx = fmap Hom <$> mctxt
                , constraintType = Hom (atom SType)
                , lhs = xty -< no natty
                , rhs = mtype
                }
              EnsureCompatibility ->
                SubtypingConstraint
                { constraintCtx = fmap Hom <$> mctxt
                , gotType = xty -< no natty
                , wantType = mtype
                }

          y <- excursion . pullUntil () $ \_ fr -> case fr of
                 Currently ty lhs rhs | lhs == FreeVar x -> Right (ty, rhs)
                 Definition name rhs | name == x -> Right (xty, rhs)
                 _ -> Left ()
          case y of
            Nothing  -> cry sol
            Just (ty, rhs) -> do
              (_, vstat) <- constrain "VarExpr" $ case synthMode of
                FindSimplest ->
                  Constraint
                  { constraintCtx = fmap Hom <$> mctxt
                  , constraintType = Hom (atom SType)
                  , lhs = ty -< no natty
                  , rhs = mtype
                  }
                EnsureCompatibility ->
                  SubtypingConstraint
                  { constraintCtx = fmap Hom <$> mctxt
                  , gotType = xty -< no natty
                  , wantType = mtype
                  }
              pushProblems [Elab sol $ Await (conjunction [xstat, vstat]) (rhs -< no (vlen mctxt))]
          newProb . Done $ FreeVar x
          run
    TypeExprTask LabMate synthMode expr | tyConstantCellEh expr -> do
      newProb . Elab sol $ ConstantCellTask synthMode expr
      run
    TypeExprTask MatLab synthMode expr | tyConstantCellEh expr -> ensureMatrix mctxt mtype >>= \case
      (rowGenTy, colGenTy, cellTy, rs, cs, stat)
        | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy -> do
          let rowTy = mk SAbel rowGenTy
          let colTy = mk SAbel colGenTy
          r <- invent r mctxt rowTy
          c <- invent c mctxt colTy
          (_, rcs) <- constrain "IsSingletonR" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList rowTy)
            , lhs = mk Sone r
            , rhs = rs
            }
          (_, ccs) <- constrain "IsSingletonC" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList colTy)
            , lhs = mk Sone c
            , rhs = cs
            }
          let task = ConstantCellTask synthMode expr
          (cellSol, cellProb) <- elab' "cell" mctxt (cellTy //^ subSnoc (sub0 (R $^ r <&> rowTy)) (R $^ c <&> colTy)) task
          extraStats <- case synthMode of
            EnsureCompatibility -> pure []
            FindSimplest -> do
              (_, rstat) <- constrain "rowtyIsOne" $ Constraint
                { constraintCtx = fmap Hom <$> mctxt
                , constraintType = Hom (atom SType)
                , lhs = rowTy
                , rhs = oneType
                }
              (_, cstat) <- constrain "coltyIsOne" $ Constraint
                { constraintCtx = fmap Hom <$> mctxt
                , constraintType = Hom (atom SType)
                , lhs = colTy
                , rhs = oneType
                }
              pure [rstat, cstat]
          pushProblems [cellProb]
          newProb . Elab sol $ Await (conjunction ([rcs, ccs] ++ extraStats)) (mk Sone cellSol)
          run

    TypeExprTask whereAmI synthMode (TyUnaryOp UInvert x) -> do
      (rowGenTy, colGenTy, cellTy, rs, cs, stat) <- ensureMatrix mctxt mtype
      case synthMode of
        EnsureCompatibility -> do
          move worried
        FindSimplest -> do
          invCellTy <- invent "invCellTy" (mctxt \\\ ("j", mk SAbel colGenTy) \\\ ("i", mk SAbel (wk rowGenTy))) (atom SType)
          {- (_, lstat) <- constrain "sameLength" $ SameLength
            { constraintCtx = fmap Hom <$> mctxt
            , leftEltType = mk SAbel rowGenTy
            , leftList = rs
            , rightEltType = mk SAbel colGenTy
            , rightList = cs
            } -}
          (_, istat) <- constrain "inverseCell" $ InverseQuantities
            { constraintCtx = fmap Hom <$> mctxt
            , rowGenType = rowGenTy
            , colGenType = colGenTy
            , cellTy = cellTy
            , invCellTy = lam "j" $ lam "i" $ invCellTy
            }
          let invTy = mk SMatrix colGenTy rowGenTy (lam "j" $ lam "i" $ invCellTy) cs rs
          (xSol, xProb) <- elab "invertee" mctxt invTy (TypeExprTask whereAmI FindSimplest <$> x)
          pushProblems [xProb]
          newProb . Elab sol $ Await (conjunction [stat, {- lstat, -} istat]) (E $^ matrixInverse (R $^ xSol <&> invTy))
          run
    TypeExprTask whereAmI synthMode (TyUnaryOp UTranspose x) -> let n = vlen mctxt in nattily n $ do
      (rowGenTy, colGenTy, cellTy, rs, cs, stat) <- ensureMatrix mctxt mtype
      ((r, c), cellTy) <- pure $ unpackCellType cellTy
      let cellTy' = lam c $ lam r $ cellTy //^ subSnoc (subSnoc (idSubst n :^ No (No (io n))) (var 0)) (var 1)
      let transposeTy = mk SMatrix colGenTy rowGenTy cellTy' cs rs
      (xSol, xProb) <- elab "transposee" mctxt transposeTy (TypeExprTask whereAmI synthMode <$> x)
      pushProblems [xProb]
      newProb . Elab sol $ Await stat (E $^ matrixTranspose (R $^ xSol <&> transposeTy))
      run
    TypeExprTask whereAmI synthMode (TyBinaryOp Plus x y) -> do
      -- TODO:
      -- 1. find the correct way of doing plus in `mtype`
      (xTy, yTy, stats) <- case synthMode of
        EnsureCompatibility -> pure (mtype, mtype, [])
        FindSimplest -> do
          xTy <- invent "xType" mctxt (atom SType)
          yTy <- invent "yType" mctxt (atom SType)
          (_ , jc) <- constrain "xyJoin" $ JoinConstraint
            { constraintCtx = fmap Hom <$> mctxt
            , leftGenType = xTy
            , rightGenType = yTy
            , joinGenType = mtype
            }
          pure (xTy, yTy, [jc])
      (xSol, xProb) <- elab "plusXTy" mctxt xTy (TypeExprTask whereAmI FindSimplest <$> x)
      (ySol, yProb) <- elab "plusYTy" mctxt yTy (TypeExprTask whereAmI FindSimplest <$> y)
      pushProblems [xProb, yProb]
      newProb . Elab sol $ Await (conjunction stats) (mk Splus xSol ySol) -- FIXME: do proper addition, eg if mtype is a matrix type
      move winning
    TypeExprTask whereAmI synthMode (TyUnaryOp UMinus x) -> do
      (_, _, _, _, _, stat) <- ensureMatrix mctxt mtype
      (xSol, xProb) <- elab "minusXTy" mctxt mtype (TypeExprTask whereAmI synthMode <$> x)
      pushProblems [xProb]
      newProb . Elab sol $ Await stat (E $^ matrixUminus (R $^ xSol <&> mtype))
      move winning
    TypeExprTask whereAmI synthMode (TyBinaryOp (Mul False{- x*y -} Times) x y) -> do
      -- Two main issues:
      -- redundancy in representation of matrices:
      -- (e.g., R C [a] [b] \r c. X vs
      -- \One One one one \_ _. X[a/r, b/c])
      -- guessing which multiplication case we are in (try them all):
      -- scalar * mx, mx * scalar, mx * mx
      -- (do we need two phase commit to metastore, local metastores?)
      rowGenTy <- invent "rowType" mctxt (atom SType)
      leftMidGenTy <- invent "middleTypeL" mctxt (atom SType)
      rightMidGenTy <- invent "middleTypeR" mctxt (atom SType)
      joinMidGenTy <- invent "middleTypeJ" mctxt (atom SType)
      colGenTy <- invent "colType" mctxt (atom SType)

      rx <- invent "rowX" mctxt (mk SList (tag SAbel [rowGenTy]))
      leftcxry <- invent "colXrowY" mctxt (mk SList (tag SAbel [leftMidGenTy]))
      rightcxry <- invent "colXrowY" mctxt (mk SList (tag SAbel [rightMidGenTy]))
      cy <- invent "colY" mctxt (mk SList (tag SAbel [colGenTy]))

      cellXTy <- invent "cellX" (mctxt \\\ ("i", mk SAbel rowGenTy) \\\ ("j", wk $ mk SAbel leftMidGenTy)) (atom SType)
      cellYTy <- invent "cellY" (mctxt \\\ ("j'", mk SAbel rightMidGenTy) \\\ ("k", wk $ mk SAbel colGenTy)) (atom SType)

      let xTy = mk SMatrix rowGenTy leftMidGenTy (lam "i" . lam "j" $ cellXTy) rx leftcxry
      let yTy = mk SMatrix rightMidGenTy colGenTy (lam "j'" . lam "k" $ cellYTy) rightcxry cy

      -- 1. Invent the cell type for the result
      cellZTy <- invent "cellZ" (mctxt \\\ ("i", mk SAbel rowGenTy) \\\ ("k", wk $ mk SAbel colGenTy)) (atom SType)
      -- 2. Construct the matrix type for the result
      let zTy = mk SMatrix rowGenTy colGenTy (lam "i" . lam "k" $ cellZTy) rx cy
      -- 3. Constrain it to the type we are checking against
      (_, zstat) <- constrain "Zmatrix" $ case synthMode of
        FindSimplest ->
          Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , lhs = zTy
          , rhs = mtype
          }
        EnsureCompatibility ->
          SubtypingConstraint
          { constraintCtx = fmap Hom <$> mctxt
          , gotType = zTy
          , wantType = mtype
          }
      -- 3.5 Find the shared type for the middle and check header compatibility.
      (_ , jc) <- constrain "middleJoins" $ JoinConstraint
        { constraintCtx = fmap Hom <$> mctxt
        , leftGenType = leftMidGenTy
        , rightGenType = rightMidGenTy
        , joinGenType = joinMidGenTy
        }
      middle <- invent "middle" mctxt (mk SAbel joinMidGenTy)
      (_, hc) <- constrain "headerCompat" $ HeadersCompatibility
        { constraintCtx = fmap Hom <$> mctxt
        , leftGenType = leftMidGenTy
        , rightGenType = rightMidGenTy
        , joinGenType = joinMidGenTy
        , joinStatus = jc
        , leftList = leftcxry
        , rightList = rightcxry
        , joinElement = middle
        }
      (xSol, xProb) <- elab "mulXTy" mctxt xTy (TypeExprTask whereAmI FindSimplest <$> x)
      (ySol, yProb) <- elab "mulYTy" mctxt yTy (TypeExprTask whereAmI FindSimplest <$> y)
      -- 4. Switch to the problem of ensuring the cell types are compatible
      let mulConstraint = ("ZMultiplicable", Multiplicable
            { constraintCtx = fmap Hom <$> mctxt
            , leftTypes = (rowGenTy, leftMidGenTy, cellXTy)
            , rightTypes = (rightMidGenTy, colGenTy, cellYTy)
            , returnCellType = cellZTy
            , joinGenType = joinMidGenTy
            , joinElement = middle
            , awaitingStatus = conjunction [hc, jc]
            })
      let stats = [jc, hc, zstat]
      (zSol, zProb) <- elab' "mulZRet" mctxt zTy (ConstrainTask whereAmI mulConstraint stats (E $^ MX $^ (R $^ xSol <&> xTy) <&> (R $^ ySol <&> yTy)))
      pushProblems [xProb, yProb, zProb]
      newProb . Elab sol $ Await (conjunction stats) zSol
      run
    TypeExprTask whereAmI _ (TyStringLiteral s) -> do
      (_, cs) <- constrain "IsListChar" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , lhs = mtype
          , rhs = mk SList (atom SChar)
          }
      newProb . Elab sol $ Await cs (ixKI mtype (lit s))
      run
    TypeExprTask MatLab synthMode (TyJux dir x (TyNil _ :<=: _)) -> do
      (rowGenTy, colGenTy, cellTy, rs, cs, tystat) <- ensureMatrix mctxt mtype
      (xSol, xProb) <- elab "nextToNil" mctxt (mk SMatrix rowGenTy colGenTy cellTy rs cs) (TypeExprTask MatLab synthMode <$> x)
      pushProblems [xProb]
      newProb . Elab sol $ Await tystat $ xSol
      run
    TypeExprTask MatLab FindSimplest (TyJux dir x y) -> let n = vlen mctxt in nattily n $ do
      (rowGenTy, colGenTy, cellTy', rs, cs, tystat) <- ensureMatrix mctxt mtype
      xTy <- invent "xType" mctxt (atom SType)
      yTy <- invent "yType" mctxt (atom SType)
      (xRowGenTy, xColGenTy, xCellTy', xrs, xcs, xTystat) <- ensureMatrix mctxt xTy
      (yRowGenTy, yColGenTy, yCellTy', yrs, ycs, yTystat) <- ensureMatrix mctxt yTy
      let ((i, j), cellTy) = unpackCellType cellTy'
      let (_, xCellTy) = unpackCellType xCellTy'
      let (_, yCellTy) = unpackCellType yCellTy'
      (xSol, xProb) <- elab "juxX" mctxt xTy (TypeExprTask MatLab FindSimplest <$> x)
      (ySol, yProb) <- elab "juxY" mctxt yTy (TypeExprTask MatLab FindSimplest <$> y)
      (_ , rj) <- constrain "rowJoin" $ JoinConstraint
        { constraintCtx = fmap Hom <$> mctxt
        , leftGenType = xRowGenTy
        , rightGenType = yRowGenTy
        , joinGenType = rowGenTy
        }
      (_ , cj) <- constrain "colJoin" $ JoinConstraint
        { constraintCtx = fmap Hom <$> mctxt
        , leftGenType = xColGenTy
        , rightGenType = yColGenTy
        , joinGenType = colGenTy
        }
      (jux, stats) <- case dir of
        Vertical -> do
          (_, rstat) <- constrain "catRows" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Het (mk SList (tag SAbel [rowGenTy])) rj (mk SList (tag SAbel [rowGenTy]))
            , lhs = rs
            , rhs = mk Splus xrs yrs
            }
          (_, sameStat) <- constrain "sameCol" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Het (mk SList (tag SAbel [colGenTy])) cj (mk SList (tag SAbel [colGenTy]))
            , lhs = cs
            , rhs = xcs
            }
          joinElt <- invent "joinElement" mctxt colGenTy
          (_, cstat) <- constrain "colCompat" $ HeadersCompatibility
            { constraintCtx = fmap Hom <$> mctxt
            , leftGenType = xColGenTy
            , rightGenType = yColGenTy
            , joinGenType = colGenTy
            , joinStatus = cj
            , leftList = xcs
            , rightList = ycs
            , joinElement = joinElt
            }
          (_, cellStat) <- constrain "cellJoin" $ JoinConstraint
            { constraintCtx = fmap Hom <$> (mctxt \\\ (i, mk SAbel rowGenTy) \\\ (j, wk $ mk SAbel colGenTy))
            , leftGenType = xCellTy
            , rightGenType = yCellTy //^ subSnoc (subSnoc (idSubst n :^ No (No (io n))) (var 1)) (R $^ (mk Splus (var 0) (wk (wk joinElt))) <&> wk (wk $ mk SAbel colGenTy))
            , joinGenType = cellTy
            }
          pure (Svjux, [rstat, sameStat, cstat, cellStat])
        Horizontal -> do
          (_, cstat) <- constrain "catCols" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Het (mk SList (tag SAbel [colGenTy])) cj (mk SList (tag SAbel [colGenTy]))
            , lhs = cs
            , rhs = mk Splus xcs ycs
            }
          (_, sameStat) <- constrain "sameRows" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Het (mk SList (tag SAbel [rowGenTy])) rj (mk SList (tag SAbel [rowGenTy]))
            , lhs = rs
            , rhs = xrs
            }
          joinElt <- invent "joinElement" mctxt rowGenTy
          (_, rstat) <- constrain "rowCompat" $ HeadersCompatibility
            { constraintCtx = fmap Hom <$> mctxt
            , leftGenType = xRowGenTy
            , rightGenType = yRowGenTy
            , joinGenType = rowGenTy
            , joinStatus = rj
            , leftList = xrs
            , rightList = yrs
            , joinElement = joinElt
            }
          (_, cellStat) <- constrain "cellJoin" $ JoinConstraint
            { constraintCtx = fmap Hom <$> (mctxt \\\ (i, mk SAbel rowGenTy) \\\ (j, wk $ mk SAbel colGenTy))
            , leftGenType = xCellTy
            , rightGenType = yCellTy //^ subSnoc (subSnoc (idSubst n :^ No (No (io n))) (R $^ (mk Splus (var 1) (wk (wk joinElt))) <&> wk (wk $ mk SAbel rowGenTy))) (var 0)
            , joinGenType = cellTy
            }
          pure (Shjux, [cstat, sameStat, rstat, cellStat])
      pushProblems [xProb, yProb]
      newProb . Elab sol $ Await (conjunction $ [tystat, xTystat, yTystat, rj, cj] ++ stats) (mk jux xSol ySol)
      run
    TypeExprTask MatLab EnsureCompatibility (TyJux dir x y) -> do
      (rowGenTy, colGenTy, cellTy, rs, cs, tystat) <- ensureMatrix mctxt mtype
      case dir of
        Vertical -> do
          rs0 <- invent "rs0" mctxt (mk SList (tag SAbel [rowGenTy]))
          rs1 <- invent "rs1" mctxt (mk SList (tag SAbel [rowGenTy]))
          (_, cstat) <- constrain "SplitRs" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList (tag SAbel [rowGenTy]))
            , lhs = mk Splus rs0 rs1
            , rhs = rs
            }
          (xSol, xProb) <- elab "vjuxTop" mctxt (mk SMatrix rowGenTy colGenTy cellTy rs0 cs) (TypeExprTask MatLab EnsureCompatibility <$> x)
          (ySol, yProb) <- elab "vjuxBot" mctxt (mk SMatrix rowGenTy colGenTy cellTy rs1 cs) (TypeExprTask MatLab EnsureCompatibility <$> y)
          pushProblems [xProb, yProb]
          let cstat' = conjunction [tystat, cstat]
          newProb . Elab sol $ Await (debugMatrix ("CStat = " ++ show cstat') cstat') $
            debugMatrix "Making vjux..." (mk Svjux xSol ySol)
          run
        Horizontal -> do
          cs0 <- invent "cs0" mctxt (mk SList (tag SAbel [colGenTy]))
          cs1 <- invent "cs1" mctxt (mk SList (tag SAbel [colGenTy]))
          (_, cstat) <- constrain "SplitCs" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList (tag SAbel [colGenTy]))
            , lhs = mk Splus cs0 cs1
            , rhs = cs
            }
          (xSol, xProb) <- elab "hjuxLeft" mctxt (mk SMatrix rowGenTy colGenTy cellTy rs cs0) (TypeExprTask MatLab EnsureCompatibility <$> x)
          (ySol, yProb) <- elab "hjuxRight" mctxt (mk SMatrix rowGenTy colGenTy cellTy rs cs1) (TypeExprTask MatLab EnsureCompatibility <$> y)
          pushProblems [xProb, yProb]
          let cstat' = conjunction [tystat, cstat]
          newProb . Elab sol $ Await (debugMatrix ("CStat = " ++ show cstat') cstat') $
            debugMatrix "Making hjux..." (mk Shjux xSol ySol)
          run
    TypeExprTask LabMate synthMode (TyJux Vertical (x :<=: src) (TyNil _ :<=: _)) | Just (SList, [e]) <- tagEh mtype -> do
      newProb $ Sourced (Elab sol (TypeExprTask LabMate synthMode x) :<=: src)
      run
    TypeExprTask LabMate synthMode (TyJux Horizontal x y) | Just (SList, [e]) <- tagEh mtype -> do
      (hSol, hProb) <- elab "head" mctxt e (TypeExprTask LabMate synthMode <$> x)
      (tSol, tProb) <- elab "tail" mctxt mtype (TypeExprTask LabMate synthMode <$> y)
      pushProblems [hProb, tProb]
      newProb . Elab sol . Await (conjunction []) $ tag Splus [mk Sone hSol, tSol]
      run
    TypeExprTask LabMate synthMode (TyNil Horizontal) | Just (SList, [e]) <- tagEh mtype -> do
      newProb . Elab sol . Await (conjunction []) $ nil `inScopeOf` mtype
      run
    TypeExprTask LabMate _ (TyAtom a) -> do
      atoms <- invent "atoms" mctxt (mk SList SAtom)
      (_ , cstat) <- constrain "listAtoms" $ Constraint
        { constraintCtx = fmap Hom <$> mctxt
        , constraintType = Hom (atom SType)
        , lhs = mk SEnum atoms
        , rhs = mtype
        }
      (_ , estat) <- constrain "elem" $ ElemConstraint
        { constraintCtx = fmap Hom <$> mctxt
        , needle = a
        , hayStack = atoms
        }
      newProb . Elab sol $ Await (conjunction [cstat, estat]) (inContext mctxt $ atom a)
      run
    TypeExprTask LabMate _ (TyBraces ma) -> do
      genTy <- invent "genTy" mctxt (atom SType)
      (_ , cstat) <- constrain "abelType" $ Constraint
        { constraintCtx = fmap Hom <$> mctxt
        , constraintType = Hom (atom SType)
        , lhs = mk SAbel genTy
        , rhs = mtype
        }
      (aSol, aProb) <- elab "abel" mctxt (mk SAbel genTy) (AbelTask <$> (fromMaybe (noSource $ TyNum 1) ma))
      pushProblems [aProb]
      newProb . Elab sol $ Await cstat aSol
      run
    TypeExprTask LabMate synthMode (TyApp f args) -> do
      fTy <- invent "fTy" mctxt (atom SType)
      (fSol, fProb) <- elab "func" mctxt fTy (TypeExprTask LabMate FindSimplest <$> f)
      pushProblems [fProb]
      newProb . Elab sol $ ElimTask (vlen mctxt) (fSol, fTy) args
      run
    ConstantCellTask synthMode (TyNum k) -> case tagEh mtype of
      Just (SList, [genTy]) -> do
        (_, cs) <- constrain "IsOne" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , lhs = genTy
          , rhs = oneType
          }
        case () of
          _ | k >= 0 -> do
            newProb . Elab sol $ Await cs (ixKI mtype (lit k))
          _ | True -> do
            cry sol
            newProb . Elab sol $ Abandon etask
        run
      Just (SAbel, [genTy]) -> do
        (_, cs) <- constrain "IsOne" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , lhs = genTy
          , rhs = oneType
          }
        newProb . Elab sol $ Await cs (ixKI mtype (lit k))
        run
      _ -> do
        newProb . Elab sol $ ConstantCellTask synthMode (TyDouble (fromIntegral k))
        run
    ConstantCellTask synthMode (TyDouble d) -> case tagEh mtype of
      Just (SQuantity, [genTy, dim]) -> case d of
        0 -> do
          metaDefn sol (inContext mctxt $ lit (0::Double))
          newProb $ Done nil
          run
        d -> do
          (_ , cstat) <- constrain "dimensionless" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SAbel genTy)
            , lhs = dim
            , rhs = nil
            }
          newProb . Elab sol $ Await cstat (inContext mctxt $ lit d)
          run
      _ -> case synthMode of
        EnsureCompatibility -> debug ("Unresolved overloading of numerical constant " ++ show d ++ " at type " ++ show mtype) $ move worried
        FindSimplest -> do
          (_, stat) <- constrain "toilTrouble" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (atom SType)
            , lhs = mtype
            , rhs = doubleType -< no (vlen mctxt)
            }
          newProb . Elab sol $ Await stat (inContext mctxt $ lit d)
          run
    ElimTask n (tgt, tty) [] -> nattyEqOi n (vlen mctxt) $ do
      (_, cstat) <- debug ("!!!ElimTask[] " ++ show tty) $ constrain "elimFits" $ Constraint
        { constraintCtx = fmap Hom <$> mctxt
        , constraintType = Hom (atom SType)
        , lhs = tty
        , rhs = mtype
        }
      newProb . Elab sol $ Await cstat tgt
      run
    ElimTask n (tgt, tty) (x : xs) -> nattyEqOi n (vlen mctxt) $ do
      tty <- debug ("!!!ElimTask before x" ++ show tty ++ " for " ++ show x) $ normalise mctxt (atom SType) tty
      case debug ("!!!ElimTask x" ++ show tty ++ " for " ++ show x) $ tagEh tty of
        Just (SPi, [s, t]) | Just t <- lamEh t -> do
          (xSol, xProb) <- elab "arg" mctxt s (TypeExprTask LabMate EnsureCompatibility <$> x)
          let tty' = t //^ sub0 (R $^ xSol <&> s)
          let tgt' = E $^ (D $^ (R $^ tgt <&> tty) <&> xSol)
          tty' <- normalise mctxt (atom SType) tty'
          tgt' <- normalise mctxt tty' tgt'
          pushProblems [xProb]
          newProb . Elab sol $ ElimTask n (tgt', tty') xs
          run
        Just _ -> do
          cry sol
          move Whacked
        Nothing -> do
          newProb . Elab sol $ ElimTask n (tgt, tty) (x : xs)
          move worried
    AbelTask t -> case t of
      TyNum 1 -> do
        metaDefn sol (inContext mctxt nil)
        newProb $ Done nil
        run
      TyBinaryOp (Mul False Times) x y -> do
        (xSol, xProb) <- elab "abelLeft" mctxt mtype (AbelTask <$> x)
        (ySol, yProb) <- elab "abelRight" mctxt mtype (AbelTask <$> y)
        pushProblems [xProb, yProb]
        metaDefn sol (mk Splus xSol ySol)
        newProb $ Done nil
        run
      TyBinaryOp (Mul False RDiv) x y -> do
        (xSol, xProb) <- elab "abelLeft" mctxt mtype (AbelTask <$> x)
        (ySol, yProb) <- elab "abelRight" mctxt mtype (AbelTask <$> y)
        pushProblems [xProb, yProb]
        metaDefn sol (mk Splus xSol (tup [lit (-1 :: Int), ySol]))
        newProb $ Done nil
        run
      TyBinaryOp (Pow False) x (TyNum n :<=: nsrc) -> do
        (xSol, xProb) <- elab "abelLeft" mctxt mtype (AbelTask <$> x)
        pushProblems [xProb]
        metaDefn sol (tup [lit n, xSol])
        newProb $ Done nil
        run
      TyBraces (Just g) | Just (SAbel, [genTy]) <- tagEh mtype -> do
        (gSol, gProb) <- elab "abelGen" mctxt genTy (TypeExprTask LabMate EnsureCompatibility <$> g)
        pushProblems [gProb]
        metaDefn sol (mk Sone gSol)
        newProb $ Done nil
        run
      TyAtom a -> do
        newProb . Elab sol $ AbelTask (TyBraces (Just (noSource t)))
        run
      t -> debug ("Abeltask falling through: " ++ show t ++ " at type " ++ show mtype ++ " context " ++ show mctxt) $ do
        newProb . Elab sol $ (TypeExprTask LabMate FindSimplest {-EnsureCompatibility-} t)
        run
    LHSTask lhs -> case lhs of
      LVar x -> do
        (x, ty) <- debug ("LVar " ++ show meta) . ensureDeclaration $
          UserDecl{ varTy = Nothing
                  , currentName = x
                  , seen = True
                  , newNames = []
                  , capturable = True
                  , whereAmI = MatLab}
        (_, ccs) <- constrain "IsLHSTy" $ Constraint
          { constraintCtx = fmap Hom <$> mctxt
          , constraintType = Hom (atom SType)
          , lhs = mk SDest (ty -< no (vlen mctxt))
          , rhs = mtype
          }
        metaDefn sol (FreeVar x -< no (vlen mctxt))
        newProb . Done $ FreeVar x
        move winning
      _ -> do  -- switch to being a scoping problem
        newProb $ LHS lhs
        run
    ExprTask whereAmI synthMode e -> case toTypeExpr' e of
      Just e -> do
        newProb . Elab sol $ TypeExprTask whereAmI synthMode e
        run
      _ -> do  -- switch to being a scoping problem
        newProb $ Expression e
        run
    Await cstatus tm -> normalise VN (atom STwo) cstatus >>= \case
      Intg 1 -> do
        metaDefn sol tm
        newProb $ Done nil
        move winning
      Intg 0 -> do
        cry sol
        debug "Found `Impossible`, switching to `Abandon`" $ newProb . Elab sol $ Abandon etask
        move Whacked
      cstatus -> do
        newProb . Elab sol $ Await cstatus tm
        move winning
    ConstrainTask whereAmI (s, constraint) stats tm -> do
      (_, cstatus) <- constrain s constraint
      newProb . Elab sol $ Await (conjunction $ cstatus:stats) tm
      run
    _ -> move worried

-- if move sees a Left fork, it should switch to Right and run
-- if move sees a Right fork, switch to Left and keep moving
-- the mood tells us the status of the fork we are inside, i.e.,
-- the frames and the problem in the state
move :: Mood -> Elab ()
move mood = pull >>= \case
  Nothing -> do
    cleanup mood
    st@MS{..} <- get
    if clock > epoch
      then do
        put st{ epoch = clock }
        run
      else do
        diagnosticRun
  Just fr -> case fr of
    Fork (Right MkFork{..}) -> do
      let (mood', store') = mood `andMood` fstatus
      case store' of
        Nothing -> pure ()
        -- confine the local store we were carrying to the largest
        -- region where it makes sense
        Just store' -> shup $ LocalStore store'
      (fframes, fprob) <- switchFwrd (fframes, fprob)
      -- after switching forward, fframes and fprob pertain to the
      -- branch, associated with the mood
      shup $ Fork (Left MkFork{fstatus = () <$ mood, ..})
      -- as we are moving out, the mood covers both forks
      move mood'
    Fork (Left MkFork{..}) -> do
      case mood of
        Winning _ store' | not (Map.null store') -> push $ LocalStore store'
        _ -> pure ()
      (fframes, fprob) <- switchFwrd (fframes, fprob)
      push $ Fork (Right MkFork{fstatus = () <$ mood, ..})
      run
    Catch MkFork{..} -> case mood of
      -- decision to commit
      Winning True ms ->
        debugCatch ("Committing with " ++ show ms) $ move mood
      -- don't commit yet, keep local store local
      Winning False ms -> debugCatch ("Winning but not committing with " ++ show ms) $ do
        unless (Map.null ms) . shup $ LocalStore ms
        shup fr
        move worried
      -- right forks are our only hope now, prune the left fork
      Whacked -> debugCatch "Whacked" $ do
        switchFwrd (fframes, fprob)
        run
    LocalNamespace ns -> do
      ns <- swapNameSupply ns
      shup $ LocalNamespace ns
      move mood
    LocalStore store -> case mood of
      Winning wonEh store' -> move (Winning wonEh (store' <> store))
      _ -> do
        shup $ LocalStore store
        move mood
    _ -> do
      fr <- normaliseFrame fr
      shup fr
      move mood

normaliseFrame :: Frame -> Elab Frame
normaliseFrame = \case
  Currently ty ltm rtm -> do
    ty  <- normalise emptyContext (atom SType) ty
    ltm <- normalise emptyContext (mk SDest ty) ltm
    rtm <- normalise emptyContext ty rtm
    pure $ Currently ty ltm rtm
  Declaration x xty -> -- propagate information from solved
                       -- metavars before we clean them up
    Declaration x <$> traverse (normalise emptyContext (atom SType)) xty
  Diagnostic rl dd -> Diagnostic rl <$> normaliseDiagnostic dd
  fr -> pure fr
  where
    normaliseDiagnostic (SynthD ty tm e) = do
      ty <- normalise VN (atom SType) ty
      tm <- normalise VN ty tm
      pure $ SynthD ty tm e
    normaliseDiagnostic (UnitD un stat tn) = do
      stat <- normalise VN (atom STwo) stat
      pure $ UnitD un stat tn
    normaliseDiagnostic d@(UnitDs _) = pure d
    normaliseDiagnostic d@(ReadFromD filename vs) = do
      vs <- traverse (either (pure . Left)
                     (\ (s, ty) -> (Right . (s,)) <$> normalise emptyContext (atom SType) ty)) vs
      pure $ ReadFromD filename vs

cleanup :: Mood -> Elab ()
cleanup mood = do
  ms <- gets metaStore
  ms <- case mood of
    Winning _ ms' -> pure $ ms' <> ms
    _ -> pure ms
  flip Map.traverseWithKey ms $ \name meta@Meta{..} -> nattily (vlen mctxt) $ do
    ctx <- traverse (traverse (normalise mctxt (atom SType))) mctxt
    ty <- normalise ctx (atom SType) mtype
    tm <- traverse (normalise ctx ty) mdefn
    let meta = Meta{ mctxt = ctx, mtype = ty, mdefn = tm, mstat = mstat }
    modify $ \st@MS{..} -> st{ metaStore = Map.insert name meta metaStore }
  --FIXME
  pure ()
  --modify $ \st@MS{..} -> st{ metaStore = Map.filter (\Meta{..} -> mstat /= Hoping || isNothing mdefn) metaStore }

-- `diagnosticRun` *never* encounters a right fork, because of the way
-- `move` leaves the tree (by the time `move` reaches the root of the
-- tree, all the forks are left forks)
diagnosticRun :: Elab ()
diagnosticRun = llup >>= \case
  Just fr -> case fr of
    Diagnostic (n, dent) dd -> do
      nt <- gets nonceTable
      msg <- msg dent dd
      traverse_ push [Source (n, Hide msg), fr]
      diagnosticRun
    _ -> push fr >> diagnosticRun
  Nothing -> diagnosticMove mempty
  where
    msg :: Int -> DiagnosticData -> Elab [Tok]
    msg dent = \case
      SynthD ty tm (e :<=: (en, _)) -> do
        let resp = [Tok "\n" Ret dump, spc dent, sym "%<", spc 1]
        statTy <- traverse metaStatus . Set.toList $ dependencies ty
        statTm <- traverse metaStatus . Set.toList $ dependencies tm
        sty <- unelabType emptyContext ty
        pure $ case (filter (<= Hoping) statTy, filter (<= Hoping) statTm) of
          ([], []) -> resp ++ [non en, spc 1, sym "::", spc 1] ++ sty
          ([], _) | Crying `elem` statTm ->
            resp ++ [non en, spc 1, sym "should have type", spc 1]
            ++ sty ++ [sym ",", spc 1, sym "but it does not"]
          ([], _) ->
            resp ++ [non en, spc 1, sym "should have type", spc 1]
            ++ sty ++ [sym ",", spc 1, sym "and it might." {- , spc 1, sym (show (dependencies tm)), spc 1, sym (show statTm)-}]
          (_, _) | Crying `elem` statTy ->
            resp ++ [sym "There is no sensible type for", spc 1, non en]
          (hopingTy, hopingTm) ->
            debug ("%%%% Puzzle" ++ show (dependencies ty) ++ " and terms " ++ show (dependencies tm)) $
              resp ++ [sym "The expression", spc 1, non en, spc 1, sym "is such a puzzle"]
      -- _ -> pure [Tok "\n" Ret dump, spc dent, sym "%<", spc 1, Tok "Goodbye" Nom dump]
      UnitD un stat tn -> case stat of
        Intg 1 -> pure
          [ Tok "\n" Ret dump
          , spc dent, sym "%<{", Tok "\n" Ret dump
          , spc dent, non un, spc 1, sym "=", spc 1, Tok "1" Dig dump, sym ";"
                    --, spc 1, sym "%", spc 1, sym "::" , spc 1, non tn
                    , Tok "\n" Ret dump
          , spc dent, sym "%<}"
          ]
        Intg 0 -> pure
          [ Tok "\n" Ret dump
          , spc dent, sym "%<", spc 1, sym "I cannot make", spc 1, non un, spc 1
                    , sym "a unit because", spc 1, non tn, spc 1, sym "is not a quantity type."
          ]
        cstat  -> pure
          [ Tok "\n" Ret dump
          , spc dent, sym "%<", spc 1, sym "I cannot make", spc 1, non un, spc 1
                    , sym "a unit yet, because I do not see why", spc 1, non tn, spc 1, sym "is a quantity type."
          ]
      UnitDs units -> pure $
          [ Tok "\n" Ret dump
          , spc dent, sym "%<{", Tok "\n" Ret dump
          , spc dent, sym "%", spc 1, sym "LabMate tells MATLAB that units are 1s", Tok "\n" Ret dump
          ] ++
          foldMap (\u ->
                    [spc dent, non (nonce u), spc 1, sym "=", spc 1, Tok "1" Dig dump, sym ";", Tok "\n" Ret dump])
          units ++
          [ spc dent, sym "%<}"
          ]
      ReadFromD filename vars -> go vars >>= \case
        Left err -> pure $ [ Tok "\n" Ret dump, spc dent, sym "%<", spc 1] ++ err
        Right code -> pure $ [ Tok "\n" Ret dump, spc dent, sym "%<{"]
                       ++ concatMap (\ x -> Tok "\n" Ret dump:spc dent:x)
                                    (preamble ++ code) ++ [ Tok "\n" Ret dump, spc dent, sym "%<}"]
       where
        preamble = [[sym ("h=fopen(\'" ++ filename ++ "\');")]
                   ,[sym "c=textscan(h,\'%f\');"]
                   ,[sym "fclose(h);"]
                   ,[sym "src = c{1};"]
                   ,[sym "readPtr = 1;"]
                   ]
        go :: [Either String (String, TYPE)] -> Elab (Either [Tok] [[Tok]])
        go [] = pure $ Right []
        go (Left err:vs) = pure $ Left [ sym err ]
        go (Right (v, ty):vs) = readFromType emptyContext v ty >>= \case
          Right code -> go vs >>= \case
            Left err -> pure $ Left $ err
            Right codes -> pure $ Right $ code ++ codes
          Left err -> pure $ Left err

        readFromType :: NATTY n => Context n -> String -> Typ ^ n -> Elab (Either [Tok] [[Tok]])
        readFromType ctx var ty = do
          ty <- normalise ctx (atom SType) ty
          case tagEh ty of
            _ | ty == doubleType -< no (scopeOf ty) -> pure $ Right $ readSingle
            Just (SAbel, [ty]) | isUnitType ty -> pure $ Right readSingle
            Just (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
              | Just (i, cellTy) <- lamNameEh cellTy, Just (j, cellTy) <- lamNameEh cellTy
              , rs <- listView rs, cs <- listView cs, all isRight rs, all isRight cs -> do
                  let ctx' = ctx \\\ (i, mk SAbel rowGenTy) \\\ (j, wk $ mk SAbel colGenTy)
                  cellTy <- normalise ctx' (atom SType) cellTy
                  case (length rs, length cs) of
                    (1, 1) -> readFromType ctx' var cellTy
                    (1, c) -> fmap (\ s -> [[sym ("for i = 1:" ++ show c)]] ++ map (spc 2:) s ++ [[sym "end"]])
                                <$> (readFromType ctx' (var ++ "(i)") cellTy)
                    (r, 1) -> fmap (\ s -> [[sym ("for i = 1:" ++ show r)]] ++ map (spc 2:) s ++ [[sym "end"]])
                                <$> (readFromType ctx' (var ++ "(i,1)") cellTy)
                    (r, c) -> fmap (\ s -> [[sym ("for i = 1:" ++ show r)], [spc 2, sym ("for j = 1:" ++ show c)]]
                                     ++ map (spc 4:) s ++ [[spc 4, sym "end"], [sym "end"]])
                                <$> (readFromType ctx' (var ++ "(i,j)") cellTy)
            Just (SQuantity, [enumTy, exp]) -> pure $ Right $ readSingle -- TODO: require unit
            _ -> do
              ty <- unelabType ctx ty
              pure $ Left ([sym "I do not know how to generate code to read from type "] ++ ty)
         where
          readSingle = [[sym (var ++ " = src(readPtr);")], [sym "readPtr = readPtr + 1;"]]

metaStatus :: Name -> Elab Status
metaStatus x = do
  ms <- gets metaStore
  case Map.lookup x ms of
    Just m -> pure (mstat m)
    Nothing -> error $ "metaStatus: " ++ show x

unelabType :: forall n . NATTY n => Context n -> Typ ^ n -> Elab [Tok]
unelabType ctx ty | Just ct <- tagEh ty = case ct of
  -- TODO: cover all types properly
  (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs]) -- 1 x 1 matrix
    | Just (i, cellTy) <- lamNameEh cellTy, Just (j, cellTy) <- lamNameEh cellTy ->
        case (rowGenTy, colGenTy, cellTy, rs, cs) of
          (_, _, _, Intg r, Intg c) -> do
            let sig = subSnoc (sub0 (R $^ nil <&> mk SAbel rowGenTy)) (R $^ nil <&> mk SAbel colGenTy)
            cellTy <- unelabType ctx =<< normalise ctx (atom SType) (cellTy //^ sig)
            case (r, c) of
              (1, 1) -> pure cellTy
              _ -> pure $ intersperse (spc 1) [sym "[", sym (show r), sym "x", sym (show c), sym "]"] ++ [spc 1] ++ cellTy
          (_, _, cellTy' :^ Su (Su th), _, _) -> do
            rs <- unelabTerm ctx (mk SList (tag SAbel [rowGenTy])) rs
            cs <- unelabTerm ctx (mk SList (tag SAbel [colGenTy])) cs
            cellTy <- unelabType (ctx \\\ (i, mk SAbel rowGenTy) \\\ (j, wk $ mk SAbel colGenTy)) cellTy
            pure $ concat
              [ intersperse (spc 1) [sym "[", sym i, sym "<-"]
              , [spc 1]
              , rs
              , [spc 1]
              , intersperse (spc 1) [sym "x", sym j, sym "<-"]
              , [spc 1]
              , cs
              , [spc 1, sym "]", spc 1]
              , cellTy
              ]
          (_, _, cellTy' :^ Su (No th), Intg r, _) -> do
            cs <- unelabTerm ctx (mk SList (tag SAbel [colGenTy])) cs
            cellTy <- unelabType (ctx \\\ (j, mk SAbel colGenTy)) (cellTy' :^ Su th)
            pure $ concat
              [ intersperse (spc 1) [sym "[", sym (show r), sym "x", sym j, sym "<-"]
              , [spc 1]
              , cs
              , [spc 1, sym "]", spc 1]
              , cellTy
              ]
          (_, _, cellTy' :^ No (Su th), _, Intg c) -> do
            rs <- unelabTerm ctx (mk SList (tag SAbel [rowGenTy])) rs
            cellTy <- unelabType (ctx \\\ (i, mk SAbel rowGenTy)) (cellTy' :^ Su th)
            pure $ concat
              [ intersperse (spc 1) [sym "[", sym i, sym "<-"]
              , [spc 1]
              , rs
              , [spc 1]
              , intersperse (spc 1) [sym "x", sym (show c), sym "]"]
              , [spc 1]
              , cellTy
              ]
          _ -> pure [sym $ show ty]
  (SAbel, [ty]) | isUnitType ty -> pure [nom "int"]
  (SList, [ty]) | Just (SChar, []) <- tagEh ty -> pure [nom "string"]
  (SEnum, [as]) -> do
    tas <- unelabTerm ctx (mk SList $ atom SAtom) as
    pure $ [sym "Enum", spc 1] ++ tas
  _ | ty == doubleType -< no (scopeOf ty) -> pure [nom "double"]
  (SQuantity, [enumTy, exp]) -> do
    texp <- unelabTerm ctx (mk SAbel enumTy) exp
    rm <- gets refoldingMap
    case enumTy of
      enumTy :^ th | Zy <- weeEnd th, Just q <- enumTy :^ Ze `Map.lookup` rm ->
           pure $ [sym q, sym "("] ++ texp ++ [sym ")"]
      _ -> do
        tenum <- unelabType ctx enumTy
        pure $ [sym "Quantity", sym "("] ++ tenum ++ [sym ",", spc 1] ++ texp ++ [sym ")"]

  _ -> pure [sym $ show ty]
unelabType ctx ty = pure [sym $ show ty]

unelabTerm :: forall n . NATTY n => Context n -> Typ ^ n -> Term Chk ^ n -> Elab [Tok]
unelabTerm ctx ty tm | Just ty <- tagEh ty = case ty of
  (SList, [genTy]) -> do
    elabTC ctx (termToNFList genTy tm) >>= \case
      Left err -> error err
      Right xs -> go ctx genTy xs False
    where
      go :: Context n -> Typ ^ n
         -> NFList n
         -> Bool -- are we in the middle of printing rights
         -> Elab [Tok]
      go ctx ty [] True = pure [sym "]"]
      go ctx ty [] False = pure [sym "[]"]
      go ctx ty [Left x] rightEh = do
        ttm <- unelabTerm ctx ty (E $^ x)
        pure $ (if rightEh then [sym "]"] else []) ++ ttm
      go ctx ty (Left x : xs) rightEh = do
        ttm <- unelabTerm ctx ty (E $^ x)
        xs <- go ctx ty xs False
        pure $ (if rightEh then [sym "]"] else []) ++ ttm ++ [ sym "++"] ++ xs
      go ctx ty (Right x : xs) rightEh = do
        ttm <- unelabTerm ctx ty x
        xs <- go ctx ty xs True
        pure $ (if rightEh then [sym "," , spc 1] else [sym "["]) ++ ttm ++ xs
  (SAbel, [genTy]) -> case tm of
    Intg 0 -> pure [sym "{}"]
    _ -> do
      tm <- go genTy tm
      pure $ [sym "{"] ++ tm ++ [sym "}"]
  (SEnum, [as]) | Intg i <- tm -> do
      as <- elabTC ctx (termToNFList (atom SAtom) as)
      case as of
        Left err -> error err
        Right as -> case indexInEnum i as of
          Just x -> unelabTerm ctx (atom SAtom) x
          Nothing -> pure [sym $ show tm]
  _ -> pure [sym $ show tm]
  where
    go genTy (E :$ V :^ th) = case th ?^ ctx of
      VN :# (v, _) -> pure [sym v]
    go genTy tm | Just (Sone, [g]) <- tagEh tm = unelabTerm ctx genTy g
    go genTy tm | Just [Intg n, t] <- tupEh tm = do
              t <- go genTy t
              pure $ case n of
                1 -> t
                _ -> t ++ [sym "^", Tok (show n) Dig dump]
    go genTy tm | Just (Splus, [x, y]) <- tagEh tm = do
       case tupEh y of
         Just [Intg n, y] | n < 0 -> do
            x <- go genTy x
            y <- go genTy (tup [lit (-n), y])
            pure $ x ++ [spc 1, sym "/", spc 1] ++ y
         _ -> case tupEh x of
                Just [Intg n, x] | n < 0 -> do
                  x <- go genTy (tup [lit (-n), x])
                  y <- go genTy y
                  pure $ y ++ [spc 1, sym "/", spc 1] ++ x
                _ -> do
                  x <- go genTy x
                  y <- go genTy y
                  pure $ y ++ [spc 1, sym "*", spc 1] ++ x
    go genTy tm = pure [sym $ show tm]
unelabTerm ctx ty (E :$ V :^ th) = case th ?^ ctx of
  VN :# (v, _) -> pure [sym v]
unelabTerm _ _ tm = pure [sym $ show tm]

diagnosticMove :: ForkCompleteStatus -> Elab ()
diagnosticMove stat = pull >>= \case
  Nothing -> pure ()
  Just fr -> case fr of
    Fork (Right MkFork{..}) -> do
      (fframes, fprob) <- switchFwrd (fframes, fprob)
      shup $ Fork (Left MkFork{fstatus = stat ,..})
      diagnosticMove $ stat <> fstatus
    Fork (Left MkFork{..})  -> do
      (fframes, fprob) <- switchFwrd (fframes, fprob)
      push $ Fork (Right MkFork{fstatus = stat, ..})
      diagnosticRun
    _ -> shup fr >> diagnosticMove stat

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
  push . Declaration fname' $
    UserDecl{ varTy = ty,  currentName = fname
            , seen = False, newNames = []
            , capturable = False, whereAmI = MatLab}
fundecl _ = pure ()
