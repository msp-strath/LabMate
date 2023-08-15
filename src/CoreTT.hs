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
pattern Sfst = "fst"
pattern Ssnd = "snd"

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
  from = (\(a, s) -> T $^ (atom a <&> g s), \f a -> k (\s -> f (a, s)))
    where (g, k) = from

instance (Mk t, NATTY n, Scope t ~ n) => Mk (Term Chk ^ n -> t) where
  type Scope (Term Chk ^ n -> t) = n
  type Uncurry (Term Chk ^ n -> t) = (Term Chk ^ n, Uncurry t)
  from = (\(a, s) -> T $^ (a <&> g s), \f a -> k (\s -> f (a, s)))
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
typeEh ty | Just ty <- E $? ty = withScope $ do
  gotTy <- synthEh ty
  subtypeEh gotTy $ atom SType
typeEh _ = fail "typeEh: not a type"

checkEh
  :: Type ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -> TC n ()  {- Ty \ni tm -}
checkEh ty tm | Just tm <- E $? tm = do
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
    Nothing | Intg _ <- tm -> checkCanEh genTy nil
    Just []  -> pure True
    Just [EOne, t] -> True <$ checkEh genTy t
    Just [EPlus, s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [Intg _, t] -> True <$ checkEh ty t
    _ -> pure False
  (SList, [genTy]) -> case tupEh tm of
    Nothing | Intg i <- tm ->
      if i >= 0 then checkCanEh genTy nil
      else fail "checkEh: Negative length list."
    Just []  -> pure True
    Just [EOne, t] -> True <$ checkEh genTy t
    Just [EPlus, s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [Intg i, t] -> propEh genTy >>= \case
      True | i >= 0 ->  True <$ checkEh ty t
      _ -> fail $ "checkEh: " ++
       (if i < 0 then "Negative length list"
        else "Scalar multiplication at non-prop type")
    _ -> pure False
  (SEnum, [as]) -> do
    nfs <- termToNFList (mk SAtom) as
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
     (Atom s', True) : us ->
       if s == s' then pure (Just ts) else checkEnumEh us tm
     _ -> fail $ "checkEnumEh: position of atom '" ++ s ++ " not determined."
  Nothing | I i :$ U :^ th <- tm -> case ts of
    (_, True) : us -> case compare i 0 of
      LT -> fail "checkEnumEh : negative tag index."
      EQ -> pure $ Just ts
      GT -> checkEnumEh us (I (i - 1) :$ U :^ th)
    _ -> fail "checkEnumEh: tag at index not determined."
  Just (Splus, [x, y]) -> do
    Just ts <- checkEnumEh ts x
    checkEnumEh ts y
  -- neutral terms
  _ | Just tm <- E $? tm -> synthEh tm >>= \ty -> do
    subtypeEh ty (tag SEnum [nfListToTerm ts])
    pure Nothing
  _ -> fail "checkEnumEh: "

synthEh
  :: Term Syn ^ n    {- t -}
  -> TC n (Type ^ n) {- t \in T, T need *not* be normal -}
synthEh (V :^ i) = typeOf i
synthEh tm | Just tm <- D $? tm, (tgt, a) <- split tm =
  tagEh <$> synthEhNorm tgt >>= \case
    Just (SPi, [s, t]) | Just t' <- lamEh t -> withScope $ do
      checkEh s a
      pure (t' //^ sub0 (R $^ a <&> s))
    Just (SSig, [s, t])
      | Atom Sfst <- a -> pure s
      | Atom Ssnd <- a, Just t' <- lamEh t -> withScope $ do
        pure (t' //^ sub0 (D $^ tgt <&> atom Sfst))
    _ -> fail "synthEh: no"
synthEh tm | Just tm <- R $? tm, (tm, ty) <- split tm =
  ty <$ typeEh ty <* checkEh ty tm
synthEh _ = fail "synthEh: no"

synthEhNorm :: Term Syn ^ n {- t -} -> TC n (NmTy ^ n) {- t \in T -}
synthEhNorm tm = synthEh tm >>= typeEval

checkNormEval
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term Chk ^ n)
checkNormEval ty tm | Just ty <- tagEh ty = withScope $ case ty of
  (SType, []) -> typeEval tm
  (SOne, []) -> pure nil
  (SAbel, [genTy]) -> nfAbelToTerm <$> termToNFAbel genTy tm
  (SList, [genTy]) -> propEh genTy >>= \case
      True  -> nfAbelToTerm <$> termToNFAbel genTy tm
      False -> nfListToTerm <$> termToNFList genTy tm
  (SEnum, [as]) -> termToNFList(mk SAtom) as >>= \x ->
      pure $ case findInEnum tm x of
        Just (i, _)  -> int i
        -- TODO : handle neutrals, reduce further
        _ -> tm
  _ -> fail "checkNormEval: unknown type"
checkNormEval _ tm | Just tm <- E $? tm =
  fst <$> evalSynth tm
checkNormEval _ _ = fail "checkNormEval: no"

checkEval
  :: Type ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Term Chk ^ n)
checkEval ty tm = do
  ty <- typeEval ty
  checkNormEval ty tm

typeEval :: Type ^ n -> TC n (NmTy ^ n)
typeEval ty | Just ty <- tagEh ty = withScope $ case ty of
  (x, []) | x `elem` [SAtom, SOne, SType] -> pure $ mk x
  (SAbel, [genTy]) -> mk SAbel <$> typeEval genTy
  (SList, [genTy]) -> mk SList <$> typeEval genTy
  (SEnum, [as]) -> mk SEnum <$> checkNormEval (mk SList (atom SAtom)) as
  (SPi, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SPi <$> typeEval s <*> (lam x <$> under s (typeEval t'))
  (SSig, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SSig <$> typeEval s <*> (lam x <$> under s (typeEval t'))
  _ -> fail "typeEval: unknown type"
typeEval ty | Just ty <- E $? ty = fst <$> evalSynth ty
typeEval _ = fail "typeEval: no"

evalSynth :: Term Syn ^ n -> TC n (Term Chk ^ n, Type ^ n)
evalSynth tm = withScope $ case tm of
  V :^ i -> (E $^ tm,) <$> typeOf i
  tm | Just tm <- R $? tm, (ty, tm) <- split tm -> do
    ty <- typeEval ty
    (, ty) <$> checkNormEval ty tm
  tm | Just tm <- D $? tm, (tgt, a) <- split tm -> do
    (tgt', ty) <- evalSynth tgt
    ty <- typeEval ty
    r <- case tagEh ty of
      Just (SPi, [s, t]) | Just t' <- lamEh t -> do
        a <- checkNormEval s a
        let sig = sub0 $ R $^ a <&> s
        case lamEh tgt of
          Nothing -> pure (E $^ D $^ (tgt <&> a))
          Just bd -> checkEval (t' //^ sig) (bd //^ sig)
      Just (SSig, [s, t])
        | Atom Sfst <- a -> case pairEh tgt' of
          Just (a, _) -> pure a
          Nothing -> pure (E $^ D $^ (tgt <&> atom Sfst))
        | Atom Ssnd <- a, Just t' <- lamEh t ->
            case pairEh tgt' of
              Just (a, b) -> do
                a <- checkNormEval s a
                let sig = sub0 $ R $^ a <&> s
                checkEval (t' //^ sig) b
              Nothing -> pure (E $^ D $^ (tgt <&> atom Ssnd))
          --pure (t' //^ sub0 (D $^ tgt <&> atom Sfst))
      _ -> fail "synthEh: eliminator for unknown type"
    pure (r, ty)
  _ -> fail "synthEh: no"

-- TODO : handle neutral x
findInEnum :: Term Chk ^ n -> NFList n -> Maybe (Integer, NFList n)
findInEnum x ts = case (tagEh x, ts) of
  (Just (s, []), (Atom s', True) : us) ->
    if s == s' then pure (0, ts)
    else do
      (n, ts) <- findInEnum x us
      pure (1 + n, ts)
  (Nothing, (_, True) : us) | I i :$ U :^ th <- x ->
    case compare i 0 of
      LT -> Nothing
      EQ -> pure (0, ts)
      GT -> do
        (n, ts) <- findInEnum (I (i - 1) :$ U :^ th) us
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
  | Intg i <- tm = withScope $ pure $ replicate (fromInteger i) (nil, True)
  | Nil    <- tm  = pure []
  | Just [EOne, t] <- tupEh tm = checkEval ty t >>= \r -> pure [(r,True)]
  | Just [EPlus, s, t] <- tupEh tm = (++) <$> termToNFList ty s <*> termToNFList ty t
termToNFList ty tm = pure [(tm, False)]

termToNFAbel
  :: Type ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFAbel n)
termToNFAbel ty tm
  | Intg i  <- tm  = pure $ NFAbel { nfConst = i, nfStuck = [] }
  | Nil <- tm  = pure mempty
  | Just res@[EOne, t] <- tupEh tm = checkEval ty t >>= \case
     Nil -> pure $ NFAbel 1 []
     _   -> withScope $ pure $ NFAbel 0 [(tup res, 1)]
  | Just [EPlus, s, t] <- tupEh tm = (<>) <$> termToNFAbel ty s <*> termToNFAbel ty t
  | Just [Intg i, t] <- tupEh tm =
      if i == 0 then pure mempty else fmap (i *) <$> termToNFAbel ty t
termToNFAbel ty tm = pure $ NFAbel 0 [(tm, 1)]

propEh :: Type ^ n -> TC n Bool
propEh ty = do
  n <- scope
  typeEval ty >>= \case
    Atom Sone -> pure True
    _         -> pure False

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
subtypeEh got want = withScope $
  case (tagEh got, tagEh want) of
    (Just (SEnum, [gs]), Just (SEnum, [ws])) -> do
      let tyA = mk SAtom
      ngs <- termToNFList tyA gs
      nws <- termToNFList tyA ws
      prefixEh tyA ngs nws
    _ -> sameEh (mk SType) (got, want)

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


test1 = let ty = mk SPi SType (lam "X" body)
            body = mk SPi (var 0) (lam "x" (E $^ var 1))
         in runTC (typeEh ty) (natty, VN)

test2 = let ty = mk SPi SType (lam "X" body)
            body = mk SPi ( var 0) (lam "x" (E $^ var 1))
            tm = lam "X" $ lam "x" (E $^ var 0)
         in runTC (checkEh ty tm) (natty, VN)

test3 = let arr :: Term Chk ^ S Z -> Term Chk ^ S Z -> Term Chk ^ S Z
            arr src (tgt :^ th) = mk SPi src (K tgt :^ th)
            ty = mk SPi SType (lam "X" body)
            body = (evar 0 `arr` evar 0) `arr` (evar 0 `arr` evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
               E $^ D $^ var 1 <&> (E $^ D $^ var 1 <&> evar 0)
         in runTC (checkEh ty tm) (natty, VN)

test4 = let arr :: Term Chk ^ S Z -> Term Chk ^ S Z -> Term Chk ^ S Z
            arr src (tgt :^ th) = mk SPi src (K tgt :^ th)
            ty = mk SPi SType (lam "X" body)
            body = (evar 0 `arr` evar 0) `arr` (evar 0  `arr` evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
         in runTC (checkEh ty tm) (natty, VN)
         -- Left "synthEh: no"

test5 = let arr :: Term Chk ^ S Z -> Term Chk ^ S Z -> Term Chk ^ S Z
            arr src (tgt :^ th) = mk SPi src (K tgt :^ th)
            ty = mk SPi SType (lam "X" body)
            body = (evar 0 `arr` evar 0) `arr` (evar 0  `arr` evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
        in runTC (checkEh ty tm) (natty, VN)
         -- Left "synthEh : no"

test6 = let arr :: Term Chk ^ S Z -> Term Chk ^ S Z -> Term Chk ^ S Z
            arr src (tgt :^ th) = mk SPi src (K tgt :^ th)
            ty = wk . wk . wk $ mk SPi SType (lam "X" body)
            body = (evar 0 `arr` evar 0) `arr` (evar 0  `arr` evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
            types = VN :# mk Sone :# mk Sone :# mk Sone
        in  testShow' <$> runTC (checkEval ty tm) (natty, types)
