module CoreTT where

import Control.Monad
import Term

newtype TC m n x =
 TC { runTC :: (Natty n, Vec n (Term m ^ n)) -> Either String x }

instance Functor (TC m n) where
  fmap k (TC f) = TC $ fmap (fmap k) f

instance Applicative (TC m n) where
  pure = return
  (<*>) = ap

instance Monad (TC m n) where
  return = TC . pure . pure
  (TC f) >>= k = TC $ \ga ->
    f ga >>= ($ ga) . runTC . k

instance MonadFail (TC m n) where
  fail  = TC . const . Left

typeOf :: (S Z <= n) -> TC m n (Term m ^ n)
typeOf i = TC $ Right . vonly . (i ?^) . snd

scope :: TC m n (Natty n)
scope = TC $ Right . fst

typeEh :: Term m ^ n -> TC m n ()
typeEh (I n :^ _) | n >= 0 = pure ()
typeEh _ = fail "Not a type"

checkEh :: Term m ^ n {- T -} -> Term m ^ n {- t -}
        -> TC m n () {- T \ni t -}
checkEh (I n :^ _) (I i :^ _) | 0 <= i && i <= n = pure ()
checkEh _ _  = fail "CheckEh fail"

propEh :: Term m ^ n  -- invariant : always a valid type
       -> TC m n Bool
propEh (I n :^ _) | n <= 2 = pure True
propEh _ = pure False

sameEh :: Term m ^ n               -- must be a type (wrt typeEh)
       -> (Term m ^ n, Term m ^ n) -- must check at that type
       -> TC m n ()
sameEh ty (t1, t2) = propEh ty >>= \case
  True  -> pure ()
  False -> case ty of
    _ -> fail "to be implemented"
