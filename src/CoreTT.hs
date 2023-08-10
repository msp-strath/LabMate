{-# LANGUAGE FunctionalDependencies, UndecidableInstances #-}
module CoreTT where

import Control.Monad
import Term
import NormalForm
import Control.Applicative

-- pattern synonyms for the type bikeshedding

pattern SType = "Type"
pattern SOne  = "One"
pattern SAbel = "Abel"
pattern SList = "List"
pattern SAtom = "Atom"
pattern SEnum = "Enum"
pattern SPi   = "Pi"
pattern SSig  = "Sigma"

pattern TyU th = A SType :^ th
pattern TyU'  <- A SType :^ _

pattern TyOne th = A SOne :^ th
pattern TyOne'  <- A SOne :^ _

pattern TyAbel th = A SAbel :^ th
pattern TyAbel'  <- A SAbel :^ _

pattern TyList th = A SList :^ th
pattern TyList'  <- A SList :^ _
pattern TyAtom th = A SAtom :^ th
pattern TyAtom'  <- A SAtom :^ _

pattern TyEnum th = A SEnum :^ th
pattern TyEnum'  <- A SEnum :^ _

pattern TyPi th = A SPi :^ th
pattern TyPi'  <- A SPi :^ _

pattern TySig th = A SSig :^ th
pattern TySig'  <- A SSig :^ _

pattern Sapp = "app"
-- FIXME : we cannot use untaged pairs as values in Sigma types
-- simultenously with tagged elimination
pattern Sfst = "fst"
pattern Ssnd = "snd"
pattern Srad = "rad"

pattern App th = A Sapp :^ th
pattern App'  <- A Sapp :^ _

pattern Fst th = A Sfst :^ th
pattern Fst'  <- A Sfst :^ _

pattern Snd th = A Ssnd :^ th
pattern Snd'  <- A Ssnd :^ _

pattern Rad th = A Srad :^ th
pattern Rad'  <- A Srad :^ _

{-
class Mk t where
  type Scope t :: Nat
  mk :: t

instance NATTY n => Mk (Term ^ n) where
  type Scope (Term ^ n) = n
  mk = Nil

instance (Mk t, n ~ Scope t) => Mk (Term ^ n -> t) where
  type Scope (Term ^ n -> t) = n
  mk tm = _
-}

class From (s :: *) (n :: Nat) (c :: *) | c -> s n where
  from :: (s -> Term ^ n, (s -> Term ^ n) -> c)
  mk :: c
  mk = k f where (f, k) = from

instance NATTY n => From () n (Term ^ n) where
  from = (\() -> Nil, ($()))

instance (NATTY n, From s n c) => From (String, s) n (String -> c) where
  from = (\(a, s) -> atom a <&> g s, \f a -> k (\s -> f (a, s)))
    where
      (g, k) = from

instance (NATTY n, From s n c) => From (Term ^ n, s) n (Term ^ n -> c) where
  from = (\(a, s) -> a <&> g s, \f a -> k (\s -> f (a, s)))
    where
      (g, k) = from
{-
foo0 :: Term ^ S (S (S Z))
foo0 = mk

foo1 :: Term ^ S (S (S Z))
foo1 = mk "Foo"

foo2 :: Term ^ S (S (S Z))
foo2 = mk "Foo" (var 0)

foo3 :: Term ^ S (S (S Z))
foo3 = mk "Foo" (var 0) (var 2)
-}

newtype TC n x =
 TC { runTC :: (Natty n, Vec n (Type ^ n)) -> Either String x }

instance Functor (TC n) where
  fmap k (TC f) = TC $ fmap (fmap k) f

instance Applicative (TC n) where
  pure = return
  (<*>) = ap

instance Alternative (TC n) where
  empty = fail ""
  TC f <|> TC g = TC $ \ ga -> case f ga of
    Left msg -> case g ga of
      Left msg' -> Left $ msg ++ msg'
      r -> r
    r -> r

instance Monad (TC n) where
  return = TC . pure . pure
  (TC f) >>= k = TC $ \ga ->
    f ga >>= ($ ga) . runTC . k

instance MonadFail (TC n) where
  fail  = TC . const . Left

typeOf :: (S Z <= n) -> TC n (Type ^ n)
typeOf i = TC $ Right . vonly . (i ?^) . snd

scope :: TC n (Natty n)
scope = TC $ Right . fst

withScope :: (NATTY n => TC n t) -> TC n t
withScope c = do
  n <- scope
  nattily n c

under
  :: Type ^ n
  -> TC (S n) a
  -> TC n a -- discharging the bound variable is the caller's problem
under ty (TC f) = TC $ \(n, ctx) -> f (Sy n, wk <$> (ctx :# ty))

typeEh :: Term ^ n -> TC n ()
typeEh TyOne' = pure ()
typeEh TyAtom' = pure ()
typeEh TyU' = pure ()
typeEh ty | Just ts <- tupEh ty = case ts of
        [TyAbel', t] -> typeEh t
        [TyList', t] -> typeEh t
        [TyEnum', t] -> withScope $ do
          n <- scope
          let th = no n
          checkEh (tup [TyList th, TyAtom th]) t
        [TyPi', s, t] | Just t' <- lamEh t -> do
          typeEh s
          under s $ typeEh t'
        [TySig', s, t] | Just t' <- lamEh t -> do
          typeEh s
          under s $ typeEh t'
        _ -> fail "Not a type"
typeEh ty  = do
  gotTy <- synthEh ty
  n <- scope
  subtypeEh gotTy $ TyU (no n)

checkEh
  :: Type ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -> TC n ()  {- Ty \ni tm -}
checkEh ty tm = do
  n <- scope
  wantTy <- typeEval ty
  isCanon <- checkCanEh wantTy tm
  if isCanon then pure () else do
    gotTy <- synthEh tm
    subtypeEh gotTy wantTy

checkCanEh
  :: NmTy ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -> TC n Bool {- Ty \ni tm -}
checkCanEh ty tm | Just x <- tagEh ty = withScope $ case x of
  (SAbel, [genTy]) -> case tupEh tm of
    Nothing | I _ :^ _ <- tm -> checkCanEh genTy Nil
    Just []  -> pure True
    Just [One', t] -> True <$ checkEh genTy t
    Just [Plus', s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [I i :^_, t] -> True <$ checkEh ty t
    _ -> pure False
  (SList, [genTy]) -> case tupEh tm of
    Nothing | I i :^ _ <- tm ->
      if i >= 0 then checkCanEh genTy Nil
      else fail "checkEh: Negative length list."
    Just []  -> pure True
    Just [One', t] -> True <$ checkEh genTy t
    Just [Plus', s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [I i :^_, t] -> propEh genTy >>= \case
      True | i >= 0 ->  True <$ checkEh ty t
      _ -> fail $ "checkEh: " ++
       (if i < 0 then "Negative length list"
        else "Scalar multiplication at non-prop type")
    _ -> pure False
  (SEnum, [as]) -> do
    n <- scope
    nfs <- termToNFList (TyAtom (no n)) as
    True <$ checkEnumEh nfs tm
  (SOne, []) -> pure True
  (SAtom, []) | A _ :^ _ <- tm -> pure True
  (SPi, [s, t]) | Just t' <- lamEh t, Just tm' <- lamEh tm ->
    True <$ under s (checkEh t' tm')
  (SSig, [s, t]) | Just t' <- lamEh t, Just (a, d) <- pairEh tm -> withScope $ do
    checkEh s a
    True <$ checkEh (t' //^ sub0 (tag Srad [a, s])) d
  (SType, []) -> True <$ typeEh tm
  _ -> pure False
checkCanEh _ _ = pure False

checkEnumEh                   -- typechecking op
  :: NFList n                 -- haystack
  -> Term ^ n                 -- needle
  -> TC n (Maybe (NFList n))  -- longest guaranteed suffix of the
                              -- haystack, starting with the needle;
                              -- returns Nothing if we cannot put plus
                              -- after.
checkEnumEh ts tm = withScope $ case tagEh tm of
  Just (s, []) -> case ts of
     (A s' :^ _, True) : us ->
       if s == s' then pure (Just ts) else checkEnumEh us tm
     _ -> fail $ "checkEnumEh: position of atom '" ++ s ++ " not determined."
  Nothing | I i :^ th <- tm -> case ts of
    (_, True) : us -> case compare i 0 of
      LT -> fail "checkEnumEh : negative tag index."
      EQ -> pure $ Just ts
      GT -> checkEnumEh us (I (i - 1) :^ th)
    _ -> fail "checkEnumEh: tag at index not determined."
  Just (Splus, [x, y]) -> do
    Just ts <- checkEnumEh ts x
    checkEnumEh ts y
  -- neutral trms
  _ -> synthEh tm >>= \ty -> do
    subtypeEh ty (tag SEnum [nfListToTerm ts])
    pure Nothing

synthEh
  :: Term ^ n        {- t -}
  -> TC n (Type ^ n) {- t \in T, T need *not* be normal -}
synthEh (V :^ i) = typeOf i
synthEh tm = case tagEh tm of
  Just (Sapp, [f, a]) -> synthEhNorm f >>= \ty -> case tagEh ty of
    Just (SPi, [s, t]) | Just t' <- lamEh t -> withScope $ do
      checkEh s a
      pure (t' //^ sub0 (tag Srad [a, s]))
    _ -> fail "synthEh: application of a non-function"
  Just (Sfst, [p]) -> synthEhNorm p >>= \ty -> case tagEh ty of
    Just (SSig, [s, _]) -> pure s
    _ -> fail "synthEh: fst projection fail"
  Just (Ssnd, [p]) -> synthEhNorm p >>= \ty -> case tagEh ty of
    Just (SSig, [s, t]) | Just t' <- lamEh t -> withScope $
      pure (t' //^ sub0 (tag Sfst [p]))
    _ -> fail "synthEh: snd projection fail"
  Just (Srad, [tm, ty]) -> ty <$ typeEh ty <* checkEh ty tm
  _ -> fail "synthEh says \"no\""

synthEhNorm :: Term ^ n {- t -} -> TC n (NmTy ^ n) {- t \in T -}
synthEhNorm tm = synthEh tm >>= typeEval

checkNormEval
  :: NmTy ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term ^ n)
checkNormEval ty tm = case ty of
  TyU'   -> typeEval tm
  TyOne' -> withScope $ pure Nil
  ty -> case tagEh ty of
    Just (SAbel, [genTy]) -> withScope $ nfAbelToTerm <$> termToNFAbel genTy tm
    Just (SList, [genTy]) -> withScope $ propEh genTy >>= \case
      True  -> nfAbelToTerm <$> termToNFAbel genTy tm
      False -> nfListToTerm <$> termToNFList genTy tm
    Just (SEnum, [as]) -> withScope $ termToNFList (At SAtom) as >>= \x ->
      pure $ case findInEnum tm x of
        Just (i, _)  -> int i
        -- TODO : handle neutrals, reduce further
        _ -> tm
    _ -> fst <$> evalSynth tm

checkEval
  :: Type ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term ^ n)
checkEval ty tm = do
  ty <- typeEval ty
  checkNormEval ty tm

typeEval :: Type ^ n -> TC n (NmTy ^ n)
typeEval ty = withScope $ case ty of
  TyU' -> pure ty
  TyOne' -> pure ty
  TyAtom' -> pure ty
  ty -> case tagEh ty of
    Just (SAbel, [genTy]) -> mk SAbel <$> typeEval genTy
    Just (SList, [genTy]) -> mk SList <$> typeEval genTy
    Just (SEnum, [as]) -> mk SEnum <$> checkNormEval (mk SList (atom SAtom)) as
    Just (SPi, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SPi <$> typeEval s <*> (lam x <$> under s (typeEval t'))
    Just (SSig, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SSig <$> typeEval s <*> (lam x <$> under s (typeEval t'))
    _ -> fst <$> evalSynth ty

evalSynth :: Term ^ n -> TC n (Term ^ n, Type ^ n)
evalSynth tm = case tm of
  V :^ i -> (tm,) <$> typeOf i
  _ -> withScope $ case tagEh tm of
    Just (Srad, [tm, ty]) -> do
      ty <- typeEval ty
      (, ty) <$> checkNormEval ty tm
    Just (Sapp, [f, a]) -> do
      (f, ty) <- evalSynth f
      ty <- typeEval ty
      (a, resTy, sig) <- case tagEh ty of
        Just (SPi, [s, t]) | Just t' <- lamEh t -> do
          a <- checkNormEval s a
          let sig = sub0 (mk Srad a s)
          pure (a, t' //^ sig, sig)
        _ -> fail "evalSynth: application of a non-function."
      (, resTy) <$> case lamEh f of
        Just bd -> checkEval resTy (bd //^ sig)
        Nothing -> pure $ mk Sapp f a
    Just (Sfst, [p]) -> do
      (p, ty) <- evalSynth p
      ty <- typeEval ty
      resTy <- case tagEh ty of
        Just (SSig, [s, _]) -> pure s
        _ -> fail "evalSynth: first projection of a non-pair."
      pure $ (, resTy) $ case pairEh p of
        Just (s, _)-> s
        Nothing -> mk Sfst p
    Just (Ssnd, [p]) -> do
      (p, ty) <- evalSynth p
      ty <- typeEval ty
      _
    _ -> _

-- TODO : handle neutral x
findInEnum :: Term ^ n -> NFList n -> Maybe (Integer, NFList n)
findInEnum x ts = case (tagEh x, ts) of
  (Just (s, []), (A s' :^ _, True) : us) ->
    if s == s' then pure (0, ts)
    else do
      (n, ts) <- findInEnum x us
      pure (1 + n, ts)
  (Nothing, (_, True) : us) | I i :^ th <- x ->
    case compare i 0 of
      LT -> Nothing
      EQ -> pure (0, ts)
      GT -> do
        (n, ts) <- findInEnum (I (i - 1) :^ th) us
        pure (1 + n, ts)
  (Just (Splus, [x,y]), _) -> do
    (n, ts) <- findInEnum x ts
    (m, ts) <- findInEnum y ts
    pure (n + m, ts)
  _ -> Nothing

termToNFList
  :: Type ^ n     -- type of generators
  -> Term ^ n
  -> TC n (NFList n)
termToNFList ty tm
  | I j :^ _ <- tm = withScope $ pure $ replicate (fromInteger j) (Nil, True)
  | A "" :^ _ <- tm  = pure []
  | Just [One', t] <- tupEh tm = checkEval ty t >>= \r -> pure [(r,True)]
  | Just [Plus', s, t] <- tupEh tm = (++) <$> termToNFList ty s <*> termToNFList ty t
termToNFList ty tm = pure [(tm, False)]

termToNFAbel
  :: Type ^ n     -- type of generators
  -> Term ^ n
  -> TC n (NFAbel n)
termToNFAbel ty tm
  | I j :^ _ <- tm  = pure $ NFAbel { nfConst = j, nfStuck = [] }
  | A "" :^ _ <- tm  = pure mempty
  | Just [One th, t] <- tupEh tm = checkEval ty t >>= \case
      A "" :^ _ -> pure $ NFAbel 1 []
      _   -> withScope $ pure $ NFAbel 0 [(tup [One th, t], 1)]
  | Just [Plus', s, t] <- tupEh tm = (<>) <$> termToNFAbel ty s <*> termToNFAbel ty t
  | Just [I j :^ _, t] <- tupEh tm =
      if j == 0 then pure mempty else fmap (j *) <$> termToNFAbel ty t
termToNFAbel ty tm = pure $ NFAbel 0 [(tm, 1)]

propEh :: Type ^ n -> TC n Bool
propEh ty = do
  n <- scope
  typeEval ty >>= \case
    TyOne' -> pure True
    _      -> pure False

sameEh
  :: Type ^ n
  -> (Term ^ n, Term ^ n) -- must check at that type
  -> TC n ()
sameEh ty (t1, t2) = propEh ty >>= \case
  True -> pure ()
  False -> do
    t1 <- checkEval ty t1
    t2 <- checkEval ty t2
    if t1 == t2 then pure () else fail "sameEh: different terms."

subtypeEh :: Type ^ n -> Type ^ n -> TC n ()
subtypeEh got want = scope >>= \n ->
  case (tagEh got, tagEh want) of
    (Just (SEnum, [gs]), Just (SEnum, [ws])) -> do
      let tyA = TyAtom (no n)
      ngs <- termToNFList tyA gs
      nws <- termToNFList tyA ws
      prefixEh tyA ngs nws
    _ -> sameEh (TyU (no n)) (got, want)

prefixEh
  :: Type ^ n  -- element type
  -> NFList n -> NFList n -> TC n ()
prefixEh _ [] bs = pure ()
prefixEh ty ((a, elemA) : as) ((b, elemB) : bs)
  | elemA == elemB = withScope $ do
      sameEh (if elemA then ty else tag SList [ty]) (a, b)
      -- TODO: move prefixEh before sameEh call?
      prefixEh ty as bs
prefixEh _ _ _ = fail "prefixEh"

test1 = let ty = tup [TyPi (no natty), TyU (no natty), lam "X" body]
            body = tup [TyPi (no natty), var 0, lam "x" (var 1)]
         in runTC (typeEh ty) (natty, VN)

test2 = let ty = tup [TyPi (no natty), TyU (no natty), lam "X" body]
            body = tup [TyPi (no natty), var 0, lam "x" (var 1)]
            tm = lam "X" $ lam "x" (var 0)
         in runTC (checkEh ty tm) (natty, VN)

test3 = let arr :: Term ^ S Z -> Term ^ S Z -> Term ^ S Z
            arr src (tgt :^ th) = tag SPi [src, K tgt :^ th]
            ty = tup [TyPi (no natty), TyU (no natty), lam "X" body]
            body = (var 0 `arr` var 0) `arr` (var 0  `arr` var 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              tag Sapp [var 1, tag Sapp [var 1, var 0]]
         in runTC (checkEh ty tm) (natty, VN)

test4 = let arr :: Term ^ S Z -> Term ^ S Z -> Term ^ S Z
            arr src (tgt :^ th) = tag SPi [src, K tgt :^ th]
            ty = tup [TyPi (no natty), TyU (no natty), lam "X" body]
            body = (var 0 `arr` var 0) `arr` (var 0  `arr` var 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              tag Sapp [var 1, tag Sapp [var 0, var 0]]
         in runTC (checkEh ty tm) (natty, VN)
         -- Left "synthEh: application of a non-function"

test5 = let arr :: Term ^ S Z -> Term ^ S Z -> Term ^ S Z
            arr src (tgt :^ th) = tag SPi [src, K tgt :^ th]
            ty = tup [TyPi (no natty), TyU (no natty), lam "X" body]
            body = (var 0 `arr` var 0) `arr` (var 0  `arr` var 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              tag Sapp [var 1, tag Sapp [var 1, var 1]]
         in runTC (checkEh ty tm) (natty, VN)
         -- Left "sameEh: different terms."
