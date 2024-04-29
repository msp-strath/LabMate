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
import Control.Monad.Reader

debug = trace
debugCatch = const id --trace
debugMatrix = trace

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
  pprint (ConstraintFrame n c) = pure ["!!!!!CONSTRAINT FRAME!!!!!", show n ++ "  " ++ show c]
  pprint fr = pure [show fr]

instance PrettyPrint MachineState where
  pprint st = do
    let (fz :<+>: fs) = position st
    lines <- pprint (fz <>> fs, problem st)
    pure (show (metaStore st) : show (constraintStore st) : lines)

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

data DeclarationType a
  = UserDecl
  { varTy :: a             -- (eventual) type
  , currentName :: String  -- current name
  , seen :: Bool           -- have we seen it in user code?
  -- requested name and how to reply (we hope of length at most 1)
  , newNames :: [(String, ResponseLocation)]
  , capturable :: Bool     -- is it capturable?
  }
  deriving (Functor, Show, Foldable, Traversable)

data ElabTask where
  TensorTask :: TensorType' -> ElabTask
  TypeExprTask :: TypeExpr' -> ElabTask
  LHSTask :: LHS' -> ElabTask
  ExprTask :: Expr' -> ElabTask
  Await :: NATTY n => ConstraintStatus -> Term Chk ^ n -> ElabTask
  ConstrainTask :: NATTY n => (String, Constraint) -> Term Chk ^ n -> ElabTask
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
    debug ("`prob` attempting to solve constrain " ++ show c) $ solveConstraint name c
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

cry :: Name -> Elab ()
cry x = do
  meta <- getMeta x
  modify $ \st@MS{..} -> st { metaStore = Map.insert x (meta{ mstat = Crying }) metaStore }

yikes :: TERM -> TERM
yikes t = T $^ atom "yikes" <&> t

tick :: Elab ()
tick =  modify $ \st@MS{..} -> st { clock = clock + 1 }

data ConstraintType' t
  = Hom t
  -- heterogenous constraint will become homogenous as soon as the
  -- named constraints have been solved
  -- TODO: replace the list of names with a closed Boolean term
  | Het t [Name] t
  deriving (Show, Functor)

type ConstraintType n = ConstraintType' (Type ^ n)

lhsType :: ConstraintType n -> Type ^ n
rhsType :: ConstraintType n -> Type ^ n

lhsType (Hom ty) = ty
lhsType (Het lty _ _) = lty

rhsType (Hom ty) = ty
rhsType (Het _ _ rty) = rty

isHom :: ConstraintType n -> Maybe (Type ^ n)
isHom (Hom ty) = Just ty
isHom _ = Nothing


-- TODO: use boolean metavariables instead, updating the
-- status then boils down to a call to `normalise`
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

type ConstraintContext n = Vec n (String, ConstraintType n)

data Constraint = forall n . Constraint
  { constraintCtx   :: ConstraintContext n
  , constraintType  :: ConstraintType n
  , constraintStatus :: ConstraintStatus
  , lhs :: Term Chk ^ n
  , rhs :: Term Chk ^ n
  }
  -- TODO: actually use it
  | forall n. Multiplicable
  { constraintCtx :: ConstraintContext n
  , constraintStatus :: ConstraintStatus
  , mulIndexTypes :: (Type ^ n, Type ^ n, Type ^ n)
  , mulDataTypes :: (Type ^ S (S n), Type ^ S (S n), Type ^ S (S n))
  }

instance Show Constraint where
  show Constraint{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", constraintType = ", show constraintType
    , ", status = ", show constraintStatus
    , ", lhs = ", show lhs
    , ", rhs = ", show rhs
    , " }"
    ]
  show Multiplicable{..} = nattily (vlen constraintCtx) $ concat
    [ "{ constraintCtx = ", show constraintCtx
    , ", status = ", show constraintStatus
    , ", mulIndexTypes = ", show mulIndexTypes
    , ", mulDataTypes = ", show mulDataTypes
    , " }"
    ]

mkConstraintType :: Type ^ n -> [Name] -> Type ^ n -> ConstraintType n
mkConstraintType lty [] rty = Hom lty
mkConstraintType lty names rty = Het lty names rty

-- TODO: purge away
getConstraintStatus :: Name -> Elab ConstraintStatus
getConstraintStatus x = do
  cstore <- gets constraintStore
  case constraintStatus <$> Map.lookup x cstore of
    Nothing -> pure Impossible
    Just Blocked -> pure $ SolvedIf [x]
    Just (SolvedIf xs) -> mconcat <$> traverse getConstraintStatus xs
    Just cstatus -> pure cstatus

-- TODO: purge away
updateConstraintStatus :: ConstraintStatus -> Elab ConstraintStatus
updateConstraintStatus (SolvedIf xs) =
  mconcat <$> traverse getConstraintStatus xs
updateConstraintStatus cs = pure cs

infixl 5 \\\\
(\\\\) :: ConstraintContext n -> (String, ConstraintType n) -> ConstraintContext (S n)
ctx \\\\ x = fmap (fmap wk) <$> ctx :# x

normalise :: Context n -> Type ^ n -> Term Chk ^ n -> Elab (Norm Chk ^ n)
normalise ctx ty tm  = elabTC ctx (checkEval ty tm) >>= \case
  Left err -> nattily (vlen ctx) $ error . concat $ ["normalise: TC error ", err, " for ", show tm, "::", show ty]
  Right tm -> pure tm

constrain :: String -> Constraint -> Elab ConstraintStatus
constrain s c | debug ("Constrain call " ++ s ++ " constraint = " ++ show c) False = undefined
constrain s c = do
  s <- metaDecl Hoping s emptyContext (atom STwo)
  solveConstraint s c

-- gets a dismounted frame, tries to solve it, remounts it
solveConstraint :: Name -> Constraint -> Elab ConstraintStatus
solveConstraint s c | debug ("Solve constrain call " ++ show s ++ " constraint = " ++ show c) False = undefined
solveConstraint s c@Constraint{..} = case (traverse (traverse isHom) constraintCtx, constraintType) of
  (Just ctx, Hom ty) -> nattily (vlen constraintCtx) $ do
    ms  <- gets metaStore
    ty  <- normalise ctx (atom SType) ty
    lhs <- normalise ctx ty lhs
    rhs <- normalise ctx ty rhs
    lhsFlexEh <- case lhs of
       E :$ (M (x, n) :$ sig) :^ th
         | Just meta@Meta{..} <- x `Map.lookup` ms
         , Just Refl <- nattyEqEh n (vlen mctxt)
         , Just Refl <- nattyEqEh n (vlen ctx) -> do
           lhs' <- normalise mctxt mtype (nattily n (wrapMeta x))
           pure (lhs == lhs')
       _ -> pure False
    rhsFlexEh <- case rhs of
       E :$ (M (x, n) :$ sig) :^ th
         | Just meta@Meta{..} <- x `Map.lookup` ms
         , Just Refl <- nattyEqEh n (vlen mctxt)
         , Just Refl <- nattyEqEh n (vlen ctx) -> do
           rhs' <- normalise mctxt mtype (nattily n (wrapMeta x))
           pure (rhs == rhs')
       _ -> pure False
    case debug ("CONSTRAIN " ++ show lhs ++ " = " ++ show rhs) (lhs, rhs) of
      _ | debug "Checking syntactic equality?" (lhs == rhs) -> debug ("Passed syn eq for " ++ show lhs ++ " =?= " ++ show rhs) (pure $ SolvedIf [])
      (E :$ (M (x, n) :$ sig) :^ th, t :^ ph)
        | Just meta@Meta{..} <- x `Map.lookup` ms
        , Hoping <- mstat
        , lhsFlexEh
        , Just Refl <- vlen mctxt `nattyEqEh` vlen ctx
        , x `Set.notMember` dependencies t ->
          case nattyEqEh n (vlen mctxt) of
            Just Refl -> do
              metaDefn x (t :^ ph)
              pure $ SolvedIf []
            _ -> error "constrain: different context lengths"
      (t :^ ph, E :$ (M (x, n) :$ sig) :^ th)
        | Just meta@Meta{..} <- x `Map.lookup` ms
        , Hoping <- mstat
        , rhsFlexEh
        , Just Refl <- vlen mctxt `nattyEqEh` vlen ctx
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
            debug ("Push Constraint n-5 " ++ show c) $ push $ ConstraintFrame s c{ constraintStatus = Impossible }
            pure Impossible
      _ | Just (lt, ls) <- tagEh lhs
        , Just (rt, rs) <- tagEh rhs
        , lt == rt -> case (lt, ls, rs) of
          (tag, [lty], [rty]) | tag `elem` [SDest, SList, SAbel] -> constrain "dest" $ Constraint
            { constraintCtx = constraintCtx
            , constraintType = constraintType
            , constraintStatus = Unstarted
            , lhs = lty
            , rhs = rty
            }
          (SMatrix, [rowTy, colTy, cellTy, rs, cs], [rowTy', colTy', cellTy', rs', cs'])
            | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy
            , Just (r', cellTy') <- lamNameEh cellTy', Just (c', cellTy') <- lamNameEh cellTy' -> do
                rstat <- constrain "rowTy" $ Constraint
                  { constraintCtx = constraintCtx
                  , constraintType = Hom (atom SType)
                  , constraintStatus = Unstarted
                  , lhs = rowTy
                  , rhs = rowTy'
                  }
                cstat <- constrain "colTy" $ Constraint
                  { constraintCtx = constraintCtx
                  , constraintType = Hom (atom SType)
                  , constraintStatus = Unstarted
                  , lhs = colTy
                  , rhs = colTy'
                  }
                case (rstat, cstat) of
                  (SolvedIf rdeps, SolvedIf cdeps) -> do
                    cellStat <- constrain "cell" $ Constraint
                      { constraintCtx = constraintCtx
                                        \\\\ (r, mkConstraintType rowTy rdeps rowTy')
                                        \\\\ (c, mkConstraintType (wk colTy) cdeps (wk colTy'))
                      , constraintType = mkConstraintType (atom SType) (rdeps <> cdeps) (atom SType)
                      , constraintStatus = Unstarted
                      , lhs = cellTy
                      , rhs = cellTy'
                      }
                    rowStat <- constrain "row" $ Constraint
                      { constraintCtx = constraintCtx
                      , constraintType = mkConstraintType (mk SList rowTy) rdeps (mk SList rowTy')
                      , constraintStatus = Unstarted
                      , lhs = rs
                      , rhs = rs'
                      }
                    colStat <- constrain "col" $ Constraint
                      { constraintCtx = constraintCtx
                      , constraintType = mkConstraintType  (mk SList colTy) cdeps (mk SList colTy')
                      , constraintStatus = Unstarted
                      , lhs = cs
                      , rhs = cs'
                      }
                    pure $ mconcat [rstat, cstat, cellStat, rowStat, colStat]
                  _ -> pure Impossible
          (Sone, [x], [y]) -> case tagEh ty of
            Just (tag, [elty]) | tag `elem` [SList, SAbel] -> constrain "singleton" $ Constraint
              { constraintCtx = constraintCtx
              , constraintType = Hom elty
              , constraintStatus = Unstarted
              , lhs = x
              , rhs = y
              }
            _ -> do
              debug ("Push Constraint n-6 " ++ show c) $ push $ ConstraintFrame s c
              pure $ case constraintStatus of
                Blocked   -> SolvedIf [s]
                Unstarted -> SolvedIf [s]
                _ -> constraintStatus
          _ -> do
            debug ("Push Constraint n-4 " ++ show c) $ push $ ConstraintFrame s c
            pure $ case constraintStatus of
              Blocked   -> SolvedIf [s]
              Unstarted -> SolvedIf [s]
              _ -> constraintStatus
      _ -> do
       debug ("Push Constraint n-3 " ++ show c) $ push $ ConstraintFrame s c
       pure $ case constraintStatus of
         Blocked   -> SolvedIf [s]
         Unstarted -> SolvedIf [s]
         _ -> constraintStatus
  _ -> do
    debug ("Push Constraint n-2 " ++ show c) $ push $ ConstraintFrame s c
    pure $ case constraintStatus of
      Blocked   -> SolvedIf [s]
      Unstarted -> SolvedIf [s]
      _ -> constraintStatus
solveConstraint s c@Multiplicable{mulDataTypes = (x, y, z), mulIndexTypes = (i, j, k), ..}
  | Just ctx <- traverse (traverse isHom) constraintCtx = nattily (vlen constraintCtx) $ do
     i <- normalise ctx (atom SType) i
     j <- normalise ctx (atom SType) j
     k <- normalise ctx (atom SType) k
     x <- normalise (ctx \\\ ("i", i) \\\ ("j", wk j)) (atom SType) x
     y <- normalise (ctx \\\ ("j", j) \\\ ("k", wk k)) (atom SType) y
     z <- normalise (ctx \\\ ("i", i) \\\ ("k", wk k)) (atom SType) z
     debug ("MULTIPLICABLE #####################" ++ show [x, y, z]) $ case (tagEh x, tagEh y, tagEh z) of
       -- TODO: matching for `No No` does not account for metavariables
       (Just (SAbel, [x' :^ (No (No th))]), Just (SAbel, [y' :^ (No (No ph))]), _) -> do
         xystat <- constrain "xy" $ Constraint
           { constraintCtx = constraintCtx
           , constraintType = Hom (atom SType)
           , constraintStatus = Unstarted
           , lhs = x' :^ th
           , rhs = y' :^ ph
           }
         zstat <- constrain "zx" $ Constraint
           { constraintCtx = constraintCtx \\\\ ("i", Hom i) \\\\ ("k", Hom $ wk k)
           , constraintType = Hom (atom SType)
           , constraintStatus = Unstarted
           , lhs = z
           , rhs = x
           }
         pure $ xystat <> zstat
       _ -> do
         debug ("Push Constraint n-1" ++ show c) $ push $ ConstraintFrame s c
         pure $ case constraintStatus of
           Blocked   -> SolvedIf [s]
           Unstarted -> SolvedIf [s]
           _ -> constraintStatus
solveConstraint s c = do
  debug ("Push Constraint n " ++ show c) $ push $ ConstraintFrame s c
  pure $ case constraintStatus c of
    Blocked   -> SolvedIf [s]
    Unstarted -> SolvedIf [s]
    _ -> constraintStatus c

constrainEqualType :: TYPE -> TYPE -> Elab ConstraintStatus
constrainEqualType lhs rhs = constrain "Q" $ Constraint
  { constraintCtx   = VN
  , constraintType  = Hom (atom SType)
  , constraintStatus = Unstarted
  , lhs = lhs
  , rhs = rhs
  }

findDeclaration :: DeclarationType (Maybe TYPE) -> Elab (Maybe (Name, TYPE))
findDeclaration UserDecl{varTy = ty, currentName = old, seen, newNames = news} = excursion (go False)
  where
  go :: Bool {- we think we are in a function -} -> Elab (Maybe (Name, TYPE))
  go b = pull >>= \case
    Nothing -> pure Nothing
    Just f -> case f of
      Locale ScriptLocale | b -> -- if we are in a function, script
        Nothing <$ push f        -- variables are out of scope
      Locale (FunctionLocale _) -> shup f >> go True -- we know we are in a function
      Declaration n u'@UserDecl{varTy = ty', currentName = old', seen = seen', newNames = news'} | old == old' -> do
        case ty of
          Just ty -> () <$ constrainEqualType ty ty'
          Nothing -> pure ()
        Just (n, ty') <$ push (Declaration n u'{seen = seen' || seen, newNames = news' ++ news})
      _ -> shup f >> go b

makeDeclaration :: DeclarationType TYPE -> Elab (Name, TYPE)
makeDeclaration d@UserDecl{varTy, currentName} = excursion $ do
  findLocale
  x <- metaDecl ProgramVar currentName emptyContext (mk SDest varTy)
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
onNearestSource f = excursion go where
  go = pull >>= \case
    Nothing -> error "Impossible: no enclosing Source frame"
    Just (Source (n, Hide ts)) -> pushSource (n, Hide $ f ts)
    Just f -> shup f >> go

metaDecl :: Status -> String -> Context n -> Type ^ n -> Elab Name
metaDecl s x ctx ty = do
   x <- fresh x
   x <$ modifyNearestStore (Map.insert x (Meta ctx ty Nothing s))

metaDeclTerm :: Status -> String -> Context n -> Type ^ n -> Elab (Term Chk ^ n)
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
    (x, _) <- ensureDeclaration (UserDecl Nothing x True [] True)
    newProb . Done $ FreeVar x
    move winning
  LHS (LMat []) -> do
    newProb $ Done nil
    move winning
  FormalParam x -> do
    ty <- invent (x ++ "Type") emptyContext (atom SType)
    (x, _) <- makeDeclaration (UserDecl ty x True [] False)
    newProb . Done $ FreeVar x
    move winning
  Expression (Var x) ->
    findDeclaration (UserDecl Nothing x True [] False) >>= \case
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
    -- TODO: optimise for the case when we know the LHS type
    ty <- invent "assignTy" emptyContext (atom SType)
    (ltm, lhsProb) <- elab "AssignLHS" emptyContext (mk SDest ty) (LHSTask <$> lhs)
    (rtm, rhsProb) <- elab "AssignRHS" emptyContext ty (ExprTask <$> rhs)
    excursion $ postRight [Currently ty ltm rtm]
    pushProblems [lhsProb]
    newProb rhsProb
    run
  Command (Direct rl (dir :<=: src)) -> do
    pushSource src
    runDirective rl dir
  Command (Function (lhs, fname :<=: _, args) cs) ->
    findDeclaration (UserDecl Nothing fname True [] False)  >>= \case
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
    ensureDeclaration (UserDecl Nothing old False [(new, rl)] True)
    newProb $ Done nil
    move winning
  DeclareAction ty name -> do
    (name, _) <- ensureDeclaration (UserDecl (Just ty) name False [] True)
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
  -- _ -> trace ("Falling through. Problem = " ++ show (problem ms)) $ move
  _ -> move worried

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
    Declare xs ty -> do
      (sol, prob) <- elab "declType" emptyContext (atom SType) (TensorTask <$> ty)
      pushProblems (Sourced . fmap (DeclareAction sol) <$> xs)
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
      push $ Diagnostic rl (SynthD ty eSol e)
      newProb eProb
      run
    _ -> move worried

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


ensureMatrixType :: Context n -> NmTy ^ n -> Elab (NmTy ^ n, NmTy ^ n, NmTy ^ n, Norm Chk ^ n, Norm Chk ^ n, ConstraintStatus)
ensureMatrixType ctxt ty
  | Just (SMatrix, [rowTy, colTy, cellTy, rs, cs]) <- tagEh ty
  {- , Just cellTy <- lamEh cellTy
  , Just cellTy <- lamEh cellTy -} = pure (rowTy, colTy, cellTy, rs, cs, mempty)
  | otherwise = nattily (vlen ctxt) $ do
      rowTy <- invent "rowType" ctxt (atom SType)
      colTy <- invent "colType" ctxt (atom SType)
      let ctxtRC = ctxt \\\ ("r", rowTy) \\\ ("c", wk colTy)
      cellTy <- lam "r" . lam "c" <$> invent "cellType" ctxtRC (atom SType)
      rs <- invent "rs" ctxt (mk SList rowTy)
      cs <- invent "cs" ctxt (mk SList colTy)
      cstat <- constrain "ensureMat" $ Constraint
        { constraintCtx = fmap Hom <$> ctxt
        , constraintType = Hom (atom SType)
        , constraintStatus = Unstarted
        , lhs = mk SMatrix rowTy colTy cellTy rs cs
        , rhs = ty
        }
      pure (rowTy, colTy, cellTy, rs, cs, cstat)

runElabTask
  :: Name
  -> Meta -- meta which carries the solution for T
  -> ElabTask -- T
  -> Elab ()
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
      pushProblems [xsProb, ysProb, eProb]
      metaDefn sol (mk SMatrix xTy yTy (lam x . lam y $ eSol) xsSol ysSol)
      newProb $ Done nil
      move winning
    TypeExprTask (TyVar Lint) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SAbel (atom SOne) -< no (vlen mctxt)
      newProb $ Done nil
      move winning
    TypeExprTask (TyVar Lstring) | Just (SType, []) <- tagEh mtype -> do
      metaDefn sol $ mk SList (atom SChar) -< no (vlen mctxt)
      newProb $ Done nil
      move winning
    TypeExprTask (TyVar x) -> -- TODO: check whether `x` is already present in the mctxt, i.e. shadowing
      findDeclaration (UserDecl Nothing x True [] False) >>= \case
        Nothing -> do
          newProb . Done $ yikes (T $^ atom "OutOfScope" <&> atom x)
          cry sol
          move Whacked
        Just (x, xty) -> do
          y <- excursion . pullUntil () $ \_ fr -> case fr of
                 Currently ty lhs rhs | lhs == FreeVar x -> Right (ty, rhs)
                 _ -> Left ()
          case y of
            Nothing  -> cry sol
            Just (ty, rhs) -> do
              xstat <- constrainEqualType ty xty
              xstat <- fmap (<> xstat) <$> constrain "VarExpr" $ Constraint
                { constraintCtx = fmap Hom <$> mctxt
                , constraintType = Hom (atom SType)
                , constraintStatus = Unstarted
                , lhs = ty -< no natty
                , rhs = mtype
                }
              pushProblems [Elab sol $ Await xstat (rhs -< no (vlen mctxt))]
          newProb . Done $ FreeVar x
          move winning
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
          pushProblems [cellProb]
          newProb . Elab sol $ Await (rcs <> ccs) (mk Sone cellSol)
          run
      _ -> debug ("Unresolved overloading of numerical constant " ++ show k)$ move worried
    TypeExprTask (TyBinaryOp Plus x y) -> do
      -- TODO:
      -- 1. make sure `mtype` admits plus
      -- 2. find the correct way of doing plus in `mtype`
      (xSol, xProb) <- elab "plusXTy" mctxt mtype (TypeExprTask <$> x)
      (ySol, yProb) <- elab "plusYTy" mctxt mtype (TypeExprTask <$> y)
      pushProblems [xProb, yProb]
      newProb . Done $ nil -- FIXME: use the solutions
      move winning
    TypeExprTask (TyBinaryOp (Mul False{- x*y -} div) x y) -> do
      -- Two main issues:
      -- redundancy in representation of matrices:
      -- (e.g., R C [a] [b] \r c. X vs
      -- \One One one one \_ _. X[a/r, b/c])
      -- guessing which multiplication case we are in (try them all):
      -- scalar * mx, mx * scalar, mx * mx
      -- (do we need two phase commit to metastore, local metastores?)
      rowTy <- invent "rowType" mctxt (atom SType)
      midTy <- invent "middleType" mctxt (atom SType)
      colTy <- invent "colType" mctxt (atom SType)

      rx <- invent "rowX" mctxt (mk SList rowTy)
      cxry <- invent "colXrowY" mctxt (mk SList midTy)
      cy <- invent "colY" mctxt (mk SList colTy)

      cellXTy <- invent "cellX" (mctxt \\\ ("i", rowTy) \\\ ("j", wk midTy)) (atom SType)
      cellYTy <- invent "cellY" (mctxt \\\ ("j'", midTy) \\\ ("k", wk colTy)) (atom SType)

      let xTy = mk SMatrix rowTy midTy (lam "i" . lam "j" $ cellXTy) rx cxry
      let yTy = mk SMatrix midTy colTy (lam "j'" . lam "k" $ cellYTy) cxry cy
      -- 1. Invent the cell type for the result
      cellZTy <- invent "cellZ" (mctxt \\\ ("i", rowTy) \\\ ("k", wk colTy)) (atom SType)
      -- 2. Construct the matrix type for the result
      let zTy = mk SMatrix rowTy colTy (lam "i" . lam "k" $ cellZTy) rx cy
      -- 3. Constrain it to the type we are checking against
      zstat <- constrain "Zmatrix" $ Constraint
        { constraintCtx = fmap Hom <$> mctxt
        , constraintType = Hom (atom SType)
        , constraintStatus = Unstarted
        , lhs = zTy
        , rhs = mtype
        }
      -- 4. Switch to the problem of ensuring the cell types are compatible
      let mulConstraint = ("ZMultiplicable", Multiplicable
            { constraintCtx = fmap Hom <$> mctxt
            , constraintStatus = Unstarted
            , mulIndexTypes = (rowTy, midTy, colTy)
            , mulDataTypes = (cellXTy, cellYTy, cellZTy)
            })
      (xSol, xProb) <- elab "mulXTy" mctxt xTy (TypeExprTask <$> x)
      (ySol, yProb) <- elab "mulYTy" mctxt yTy (TypeExprTask <$> y)
      (zSol, zProb) <- elab' "mulZRet" mctxt zTy (ConstrainTask mulConstraint (E $^ MX $^ (R $^ xSol <&> xTy) <&> (R $^ ySol <&> yTy)))
      pushProblems [xProb, yProb, zProb]
      newProb . Elab sol $ Await zstat zSol
      run
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
      _ -> move worried
    TypeExprTask (TyJux dir x y) -> do
      (rowTy, colTy, cellTy, rs, cs, tystat) <- ensureMatrixType mctxt mtype
      case dir of
        Vertical -> do
          rs0 <- debugMatrix ("VJUX matrix #### " ++ show mtype) $ invent "rs0" mctxt (mk SList rowTy)
          rs1 <- invent "rs1" mctxt (mk SList rowTy)
          cstat <- fmap (<> tystat) $ constrain "SplitRs" $ Constraint
            { constraintCtx = fmap Hom <$> mctxt
            , constraintType = Hom (mk SList rowTy)
            , constraintStatus = Unstarted
            , lhs = mk Splus rs0 rs1
            , rhs = rs
            }
          (xSol, xProb) <- elab "vjuxTop" mctxt (mk SMatrix rowTy colTy cellTy rs0 cs) (TypeExprTask <$> x)
          (ySol, yProb) <- elab "vjuxBot" mctxt (mk SMatrix rowTy colTy cellTy rs1 cs) (TypeExprTask <$> y)
          pushProblems [xProb, yProb]
          newProb . Elab sol $ Await (debugMatrix ("CStat = " ++ show cstat) cstat) $ debugMatrix "Making vjux..." (mk Svjux xSol ySol)
          run
        Horizontal -> move worried
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
        metaDefn sol (FreeVar x -< no (vlen mctxt))
        newProb . Done $ FreeVar x
        move winning
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
        move winning
      Impossible -> do
        cry sol
        newProb . Elab sol $ Abandon etask
        move Whacked
      cstatus -> do
        newProb . Elab sol $ Await cstatus tm
        move winning
    ConstrainTask (cname, constraint) tm -> do
      cstatus <- constrain cname constraint
      newProb . Elab sol $ Await cstatus tm
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
      ty <- normalise emptyContext (atom SType) ty
      tm <- normalise emptyContext ty tm
      pure $ SynthD ty tm e

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

diagnosticRun :: Elab ()
diagnosticRun = llup >>= \case
  Just fr -> case fr of
    Diagnostic (n, dent) dd-> do
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
        sty <- unelabType ty
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
          (_, _) ->
            resp ++ [sym "The expression", spc 1, non en, spc 1, sym "is quite a puzzle"]
      _ -> pure [Tok "\n" Ret dump, spc dent, sym "%<", spc 1, Tok "Goodbye" Nom dump]

metaStatus :: Name -> Elab Status
metaStatus x = do
  ms <- gets metaStore
  case Map.lookup x ms of
    Just m -> pure (mstat m)
    Nothing -> error $ "metaStatus: " ++ show x

unelabType :: TYPE -> Elab [Tok]
unelabType ty | Just ct <- tagEh ty = case ct of
  -- TODO: cover all types properly
  (SMatrix, [rowTy, colTy, cellTy, Intg 1, Intg 1]) -- 1 x 1 matrix
    | Just cellTy <- lamEh cellTy, Just cellTy <- lamEh cellTy -> do
        let sig = subSnoc (sub0 (R $^ nil <&> rowTy)) (R $^ nil <&> colTy)
        unelabType =<< normalise emptyContext (atom SType) (cellTy //^ sig)
  (SAbel, [ty]) | Just (SOne, []) <- tagEh ty -> pure [nom "int"]
  _ -> pure [sym $ show ty]
unelabType ty = pure [sym $ show ty]

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
  push $ Declaration fname' (UserDecl ty fname False [] False)
fundecl _ = pure ()
