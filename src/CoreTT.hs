{-# LANGUAGE UndecidableInstances #-}
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

pattern TyU th = A SType :$ U :^ th
pattern TyU'  <- A SType :$ U :^ _

pattern TyOne th = A SOne :$ U :^ th
pattern TyOne'  <- A SOne :$ U :^ _

pattern TyAbel th = A SAbel :$ U :^ th
pattern TyAbel'  <- A SAbel :$ U :^ _

pattern TyList th = A SList :$ U :^ th
pattern TyList'  <- A SList :$ U :^ _
pattern TyAtom th = A SAtom :$ U :^ th
pattern TyAtom'  <- A SAtom :$ U :^ _

pattern TyEnum th = A SEnum :$ U :^ th
pattern TyEnum'  <- A SEnum :$ U :^ _

pattern TyPi th = A SPi :$ U :^ th
pattern TyPi'  <- A SPi :$ U :^ _

pattern TySig th = A SSig :$ U :^ th
pattern TySig'  <- A SSig :$ U :^ _

pattern Sfst = "fst"
pattern Ssnd = "snd"

pattern Fst th = A Sfst :$ U :^ th
pattern Fst'  <- A Sfst :$ U :^ _

pattern Snd th = A Ssnd :$ U :^ th
pattern Snd'  <- A Ssnd :$ U :^ _


class Mk t where
  type Scope t :: Nat
  type Uncurry t :: *

  from :: (Uncurry t -> Term Chk ^ Scope t, (Uncurry t -> Term Chk ^ Scope t) -> t)

  mk :: t
  mk = k f where (f, k) = from

instance (NATTY n) => Mk (Term Chk ^ n) where
  type Scope (Term Chk ^ n) = n
  type Uncurry (Term Chk ^ n) = ()
  from = (\() -> nil, ($()))

instance (Mk t, NATTY (Scope t)) => Mk (String -> t) where
  type Scope (String -> t) = Scope t
  type Uncurry (String -> t) = (String, Uncurry t)
  from = (\(a, s) -> T $^ atom a <&> g s, \f a -> k (\s -> f (a, s)))
    where (g, k) = from

instance (Mk t, NATTY n, Scope t ~ n) => Mk (Term Chk ^ n -> t) where
  type Scope (Term Chk ^ n -> t) = n
  type Uncurry (Term Chk ^ n -> t) = (Term Chk ^ n, Uncurry t)
  from = (\(a, s) -> T $^ a <&> g s, \f a -> k (\s -> f (a, s)))
    where (g, k) = from

instance (Mk t, NATTY n, Scope t ~ n) => Mk (Term Syn ^ n -> t) where
  type Scope (Term Syn ^ n -> t) = n
  type Uncurry (Term Syn ^ n -> t) = (Term Syn ^ n, Uncurry t)
  from = (\(a, s) -> T $^ (E $^ a) <&> g s, \f a -> k (\s -> f (a, s)))
    where (g, k) = from


foo0 :: Term Chk ^ S (S (S Z))
foo0 = mk

foo1 :: Term Chk ^ S (S (S Z))
foo1 = mk "Foo"

foo2 :: Term Chk ^ S (S (S Z))
foo2 = mk "Foo" (var 0)

foo3 :: Term Chk ^ S (S (S Z))
foo3 = mk "Foo" (var 0) (var 2)


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

typeEh :: Term Chk ^ n -> TC n ()
typeEh TyOne' = pure ()
typeEh TyAtom' = pure ()
typeEh TyU' = pure ()
typeEh ty | Just cts <- tagEh ty = case cts of
        (SOne, [])   -> pure ()
        (SAtom, [])  -> pure ()
        (SType, [])  -> pure ()
        (SAbel, [t]) -> typeEh t
        (SList, [t]) -> typeEh t
        (SEnum, [t]) -> withScope $
          checkEh (mk SList $ atom SAtom) t
        (SPi, [s, t]) | Just t' <- lamEh t -> do
          typeEh s
          under s $ typeEh t'
        (SSig, [s, t]) | Just t' <- lamEh t -> do
          typeEh s
          under s $ typeEh t'
        _ -> fail "typeEh: not a type"
typeEh t | Just ty <- E $? t  = withScope $ do
  gotTy <- synthEh ty
  subtypeEh gotTy $ atom SType
typeEh t = fail "typeEh: not a type"

checkEh
  :: Type ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -> TC n ()  {- Ty \ni tm -}
checkEh ty t | Just tm <- E $? t = do
    gotTy <- synthEh tm
    subtypeEh gotTy ty
checkEh ty tm = do
  wantTy <- typeEval ty
  isCanon <- checkCanEh wantTy tm
  if isCanon then pure ()
             else fail "checkEh: no"

checkCanEh
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -> TC n Bool {- Ty \ni tm -}
checkCanEh ty tm | Just x <- tagEh ty = withScope $ case x of
  (SAbel, [genTy]) -> case tupEh tm of
    Nothing | I _ :$ U :^ _ <- tm -> checkCanEh genTy nil
    Just []  -> pure True
    Just [EOne', t] -> True <$ checkEh genTy t
    Just [EPlus', s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [I i :$ U :^_, t] -> True <$ checkEh ty t
    _ -> pure False
  (SList, [genTy]) -> case tupEh tm of
    Nothing | I i :$ U :^ _ <- tm ->
      if i >= 0 then checkCanEh genTy nil
      else fail "checkEh: Negative length list."
    Just []  -> pure True
    Just [EOne', t] -> True <$ checkEh genTy t
    Just [EPlus', s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [I i :$ U :^_, t] -> propEh genTy >>= \case
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
  (SAtom, []) | A _ :$ U :^ _ <- tm -> pure True
  (SPi, [s, t]) | Just t' <- lamEh t, Just tm' <- lamEh tm ->
    True <$ under s (checkEh t' tm')
  (SSig, [s, t]) | Just t' <- lamEh t, Just (a, d) <- pairEh tm -> withScope $ do
    checkEh s a
    True <$ checkEh (t' //^ sub0 (R $^ a <&> s)) d
  (SType, []) -> True <$ typeEh tm
  _ -> pure False
checkCanEh _ _ = pure False

--

checkEnumEh                   -- typechecking op
  :: NFList n                 -- haystack
  -> Term Chk ^ n             -- needle
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
  :: Term Syn ^ n    {- t -}
  -> TC n (Type ^ n) {- t \in T, T need *not* be normal -}
synthEh (V :^ i) = typeOf i
synthEh tm = case tagEh tm of
  Just ("", [f, a]) -> synthEhNorm f >>= \ty -> case tagEh ty of
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
  Just ("", [tm, ty]) -> ty <$ typeEh ty <* checkEh ty tm
  _ -> fail "synthEh says \"no\""

synthEhNorm :: Term Syn ^ n {- t -} -> TC n (NmTy ^ n) {- t \in T -}
synthEhNorm tm = synthEh tm >>= typeEval

checkNormEval
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term Chk ^ n)
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
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term Chk ^ n)
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

evalSynth :: Term Syn ^ n -> TC n (Term Chk ^ n, Type ^ n)
evalSynth tm = case tm of
  V :^ i -> (tm,) <$> typeOf i
  _ -> withScope $ case tagEh tm of
    Just ("", [tm, ty]) -> do
      ty <- typeEval ty
      (, ty) <$> checkNormEval ty tm
    Just ("", [f, a]) -> do
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
      undefined    -- TODO: FIXME
    _ -> undefined -- TODO: FIXME

-- TODO : handle neutral x
findInEnum :: Term Chk ^ n -> NFList n -> Maybe (Integer, NFList n)
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
  -> Term Chk ^ n
  -> TC n (NFList n)
termToNFList ty tm
  | I j :^ _ <- tm = withScope $ pure $ replicate (fromInteger j) (Nil, True)
  | A "" :^ _ <- tm  = pure []
  | Just [EOne', t] <- tupEh tm = checkEval ty t >>= \r -> pure [(r,True)]
  | Just [EPlus', s, t] <- tupEh tm = (++) <$> termToNFList ty s <*> termToNFList ty t
termToNFList ty tm = pure [(tm, False)]

termToNFAbel
  :: Type ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFAbel n)
termToNFAbel ty tm
  | I j :^ _ <- tm  = pure $ NFAbel { nfConst = j, nfStuck = [] }
  | A "" :^ _ <- tm  = pure mempty
  | Just [EOne th, t] <- tupEh tm = checkEval ty t >>= \case
      A "" :^ _ -> pure $ NFAbel 1 []
      _   -> withScope $ pure $ NFAbel 0 [(tup [One th, t], 1)]
  | Just [EPlus', s, t] <- tupEh tm = (<>) <$> termToNFAbel ty s <*> termToNFAbel ty t
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
  -> (Term Chk ^ n, Term Chk ^ n) -- must check at that type
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
{-
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
-}
