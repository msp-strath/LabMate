module CoreTT where

import Control.Monad
import Term

-- pattern synonyms for the type bikeshedding

pattern TyInteger th = A "Integer" :^ th
pattern Plus th = A "plus" :^ th
pattern TyU th = A "Type" :^ th

newtype TC n x =
 TC { runTC :: (Natty n, Vec n (Term ^ n)) -> Either String x }

instance Functor (TC n) where
  fmap k (TC f) = TC $ fmap (fmap k) f

instance Applicative (TC n) where
  pure = return
  (<*>) = ap

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

typeEh :: Term ^ n -> TC n ()
typeEh (TyInteger _) = pure ()
typeEh _ = fail "Not a type"

checkEh :: Term ^ n {- Ty -}
        -> Term ^ n {- tm -}
        -> TC n () {- Ty \ni tm -}
checkEh ty@(TyInteger _) tm
  | I i :^ _ <- tm = pure ()
  | Just [Plus _, s, t] <- tupEh tm = () <$ checkEh ty s <* checkEh ty t
  | Just [I i :^ _, t] <- tupEh tm = checkEh ty t

checkEh wantTy tm  = do
  gotTy <- synthEh tm
  subtypeEh gotTy wantTy

synthEh :: Term ^ n {- t -} -> TC n (Term ^ n) {- t \in T -}
synthEh (V :^ i) = typeOf i
synthEh tm = fail "synthEh says \"no\""

checkEval :: forall n m . NATTY n
          => Term ^ n {- Ty -}
          -> Term ^ n {- tm -}
          -- must be Ty \ni tm, i.e. already checked
          -> Term ^ n
checkEval (TyInteger _) tm = nfIntegerToTerm . termToNFInteger $ tm
checkEval _ tm = tm

data NFInteger' t i = NFInteger
 { nfConst :: i
 , nfStuck :: [(t, i)] -- terms should be sorted
 } deriving (Functor)

type NFInteger m n = NFInteger' (Term ^ n) Integer

instance (Ord t, Num i, Eq i) => Semigroup (NFInteger' t i) where
  (<>) = mappend

instance (Ord t, Num i, Eq i) => Monoid (NFInteger' t i) where
  mempty = NFInteger {nfConst = 0, nfStuck = []}
  NFInteger x xtis `mappend` NFInteger y ytis = NFInteger
    { nfConst = x + y
    , nfStuck = go xtis ytis
    }
    where
      go [] ytis = ytis
      go xtis [] = xtis
      go x@(xh@(xt, xi) : xtis) y@(yh@(yt, yi) : ytis) = case compare xt yt of
        LT -> xh : go xtis y
        EQ -> ($ go xtis ytis) $ case xi + yi of
          0 -> id
          k -> ((xt, k) :)
        GT -> yh : go x ytis

nfIntegerToTerm :: NATTY n => NFInteger m n -> Term ^ n
nfIntegerToTerm NFInteger{..} = case (nfConst, nfStuck) of
  (i, []) -> int i
  (0, tis) -> go tis
  (i, tis) -> tup [Plus (no natty) , int i, go tis]
  where
    go [(tm, i)] = tup [int i, tm]
    go ((tm, i) : tis) = tup [Plus (no natty), tup [int i, tm], go tis]
    go [] = error "impossible"

termToNFInteger :: Term ^ n -> NFInteger m n
termToNFInteger tm
  | I j :^ _ <- tm  = NFInteger { nfConst = j, nfStuck = [] }
  | Just [Plus th, s, t] <- tupEh tm = termToNFInteger s <> termToNFInteger t
  | Just [I j :^ _, t] <- tupEh tm =
      if j == 0 then mempty else (j *) <$> termToNFInteger t

termToNFInteger tm = NFInteger 0 [(tm, 1)]

propEh :: Term ^ n  -- invariant : always a valid type
       -> TC n Bool
propEh _ = pure False

sameEh :: Term ^ n               -- must be a type (wrt typeEh)
       -> (Term ^ n, Term ^ n) -- must check at that type
       -> TC n ()
sameEh ty (t1, t2) = propEh ty >>= \case
  True  -> pure ()
  False -> case ty of
    _ -> fail "to be implemented"

subtypeEh :: Term ^ n -> Term ^ n -> TC n ()
subtypeEh got want = scope >>= \n ->
  sameEh (TyU (no n)) (got, want)
