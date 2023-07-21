module CoreTT where

import Control.Monad
import Term
import NormalForm
import Control.Applicative

-- pattern synonyms for the type bikeshedding

pattern SType = "Type"
pattern SOne = "One"
pattern SAbel = "Abel"
pattern SList = "List"
pattern SAtom = "Atom"
pattern SEnum = "Enum"

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

newtype TC n x =
 TC { runTC :: (Natty n, Vec n (Term ^ n)) -> Either String x }

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

typeOf :: (S Z <= n) -> TC n (Term ^ n)
typeOf i = TC $ Right . vonly . (i ?^) . snd

scope :: TC n (Natty n)
scope = TC $ Right . fst

withScope :: (NATTY n => TC n t) -> TC n t
withScope c = do
  n <- scope
  nattily n c

typeEh :: Term ^ n -> TC n ()
typeEh TyOne' = pure ()
typeEh TyAtom' = pure ()
typeEh ty | Just ts <- tupEh ty = case ts of
        [TyAbel', t] -> typeEh t
        [TyList', t] -> typeEh t
        [TyEnum', t] -> withScope $ let n = no natty
                                    in checkEh (tup [TyList n, TyAtom n]) t
        _ -> fail "Not a type"
typeEh ty  = do
  gotTy <- synthEh ty
  withScope $ subtypeEh gotTy $ TyU (no natty)

checkEh
  :: Type ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -> TC n ()  {- Ty \ni tm -}
checkEh ty tm = do
  wantTy <- withScope $ pure $ checkEval (TyU (no natty)) ty
  isCanon <- checkCanEh wantTy tm
  if isCanon then pure () else do
    gotTy <- synthEh tm
    subtypeEh gotTy wantTy

checkCanEh
  :: Type ^ n {- Ty -}
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
    Just [I i :^_, t] ->  do
      let isProp = propEh genTy
      if isProp && i >= 0 then True <$ checkEh ty t
      else fail $ "checkEh: " ++
       (if i < 0 then "Negative length list"
        else "Scalar multiplication at non-prop type")
    _ -> pure False
  (SEnum, [as]) -> do
    let nfs = termToNFList (TyAtom (no natty)) as
    True <$ checkEnumEh nfs tm
  (SOne, []) -> pure True
  (SAtom, []) | A _ :^ _ <- tm -> pure True
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

synthEh :: Term ^ n {- t -} -> TC n (Type ^ n) {- t \in T -}
synthEh (V :^ i) = typeOf i
synthEh tm = fail "synthEh says \"no\""

checkEval
  :: NATTY n
  => Type ^ n {- Ty -}
  -> Term ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> Term ^ n
checkEval ty tm
  | Just [TyAbel', genTy] <- tupEh ty = nfAbelToTerm . termToNFAbel genTy $ tm
  | Just [TyList', genTy] <- tupEh ty = if propEh genTy
      then nfAbelToTerm . termToNFAbel genTy $ tm
      else nfListToTerm . termToNFList genTy $ tm
  | Just [TyEnum', as] <- tupEh ty = case findInEnum tm (termToNFList (At SAtom) as) of
       Just (i, _)  -> int i
       -- TODO : handle neutrals, reduce further
       _ -> tm
checkEval TyOne' _ = Nil
checkEval _ tm = tm

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
  :: NATTY n
  => Type ^ n     -- type of generators
  -> Term ^ n
  -> NFList n
termToNFList ty tm
  | I j :^ _ <- tm = replicate (fromInteger j) (Nil, True)
  | Nil <- tm  = []
  | Just [One', t] <- tupEh tm = [(checkEval ty t, True)]
  | Just [Plus', s, t] <- tupEh tm = termToNFList ty s ++ termToNFList ty t
termToNFList ty tm = [(tm, False)]

termToNFAbel
  :: NATTY n
  => Type ^ n     -- type of generators
  -> Term ^ n
  -> NFAbel n
termToNFAbel ty tm
  | I j :^ _ <- tm  = NFAbel { nfConst = j, nfStuck = [] }
  | Nil <- tm  = mempty
  | Just [One th, t] <- tupEh tm = case checkEval ty t of
      Nil -> NFAbel 1 []
      _   -> NFAbel 0 [(tup [One th, t], 1)]
  | Just [Plus', s, t] <- tupEh tm = termToNFAbel ty s <> termToNFAbel ty t
  | Just [I j :^ _, t] <- tupEh tm =
      if j == 0 then mempty else (j *) <$> termToNFAbel ty t
termToNFAbel ty tm = NFAbel 0 [(tm, 1)]

propEh :: NATTY n => Type ^ n -> Bool
propEh ty = case checkEval (TyU (no natty)) ty of
   TyOne' -> True
   _      -> False

sameEh
  :: Type ^ n
  -> (Term ^ n, Term ^ n) -- must check at that type
  -> TC n ()
sameEh ty (t1, t2) = withScope $
  if propEh ty || checkEval ty t1 == checkEval ty t2 then pure ()
  else fail "sameEh : different terms."

subtypeEh :: Type ^ n -> Type ^ n -> TC n ()
subtypeEh got want = scope >>= \n -> nattily n $
  case (tagEh got, tagEh want) of
    (Just (SEnum, [gs]), Just (SEnum, [ws])) -> do
      let tyA = TyAtom (no n)
      let ngs = termToNFList tyA gs
      let nws = termToNFList tyA ws
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
