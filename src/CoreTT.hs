module CoreTT where

import Control.Monad
import Term
import NormalForm

-- pattern synonyms for the type bikeshedding

pattern TyInteger th = A "Integer" :^ th
pattern TyInteger'  <- A "Integer" :^ _

pattern TyU th = A "Type" :^ th
pattern TyU'  <- A "Type" :^ _

pattern TyOne th = A "One" :^ th
pattern TyOne'  <- A "One" :^ _

pattern TyAbel th = A "Abel" :^ th
pattern TyAbel'  <- A "Abel" :^ _

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

withScope :: (NATTY n => TC n t) -> TC n t
withScope c = do
  n <- scope
  nattily n c

typeEh :: Term ^ n -> TC n ()
typeEh TyInteger' = pure ()
typeEh TyOne' = pure ()
typeEh ty | Just [TyAbel', t] <- tupEh ty = typeEh t
typeEh _ = fail "Not a type"

checkEh :: Type ^ n {- Ty -}
        -> Term ^ n {- tm -}
        -> TC n ()  {- Ty \ni tm -}
checkEh ty@TyInteger' tm
  | I i :^ _ <- tm = pure ()
  | Just [Plus', s, t] <- tupEh tm = () <$ checkEh ty s <* checkEh ty t
  | Just [I i :^ _, t] <- tupEh tm = checkEh ty t
checkEh ty tm
  | Just [TyAbel', genTy] <- tupEh ty, I _ :^ _ <- tm
  = withScope $ checkEh genTy Nil
  | Just [TyAbel', genTy] <- tupEh ty, Just [Abel', t] <- tupEh tm
  = checkEh genTy t
  | Just [TyAbel', _] <- tupEh ty, Just [Plus', s, t] <- tupEh tm
  = () <$ checkEh ty s <* checkEh ty t
  | Just [TyAbel', _] <- tupEh ty, Just [I i :^ _, t] <- tupEh tm
  = checkEh ty t
checkEh TyOne' _ = pure ()
checkEh wantTy tm  = do
  gotTy <- synthEh tm
  subtypeEh gotTy wantTy

synthEh :: Term ^ n {- t -} -> TC n (Type ^ n) {- t \in T -}
synthEh (V :^ i) = typeOf i
synthEh tm = fail "synthEh says \"no\""

checkEval :: NATTY n
          => Type ^ n {- Ty -}
          -> Term ^ n {- tm -}
          -- must be Ty \ni tm, i.e. already checked
          -> Term ^ n
checkEval (TyInteger th) tm = nfIntegerToTerm . termToNFInteger (TyOne th) $ tm
checkEval ty tm
  | Just [TyAbel', genTy] <- tupEh ty = nfIntegerToTerm . termToNFInteger genTy $ tm
checkEval TyOne' _ = Nil
checkEval _ tm = tm

termToNFInteger :: NATTY n
                => Type ^ n       -- type of generators
                -> Term ^ n
                -> NFInteger m n
termToNFInteger ty tm
  | I j :^ _ <- tm  = NFInteger { nfConst = j, nfStuck = [] }
  | Just [Abel th, t] <- tupEh tm = case checkEval ty t of
      Nil -> NFInteger 1 []
      _   -> NFInteger 0 [(tup [Abel th, t], 1)]
  | Just [Plus', s, t] <- tupEh tm = termToNFInteger ty s <> termToNFInteger ty t
  | Just [I j :^ _, t] <- tupEh tm =
      if j == 0 then mempty else (j *) <$> termToNFInteger ty t
termToNFInteger ty tm = NFInteger 0 [(tm, 1)]

propEh :: Type ^ n -> TC n Bool
propEh TyOne' = pure True
propEh _ = pure False

sameEh :: Type ^ n
       -> (Term ^ n, Term ^ n) -- must check at that type
       -> TC n ()
sameEh ty (t1, t2) = propEh ty >>= \case
  True  -> pure ()
  False -> case ty of
    _ -> fail "to be implemented"

subtypeEh :: Type ^ n -> Type ^ n -> TC n ()
subtypeEh got want = scope >>= \n ->
  sameEh (TyU (no n)) (got, want)

-- tests
test0 = let ty = tup [TyAbel (no natty), TyOne (no natty)]
            tm = var 0 + var 1
        in testShow $ checkEval ty tm
        -- ['plus y x]

test1 = let ty = tup [TyAbel (no natty), TyOne (no natty)]
            tm = var 1 + var 0
        in testShow $ checkEval ty tm
        -- ['plus y x]

test2 = let ty = tup [TyAbel (no natty), TyOne (no natty)]
            tm = var 0 + var 0
        in testShow $ checkEval ty tm
        -- [2 x]

test3 = let ty = tup [TyAbel (no natty), TyOne (no natty)]
            tm = (var 0 + 3) + var 0
        in testShow $ checkEval ty tm
        -- ['plus 3 [2 x]]

test4 = let ty = tup [TyAbel (no natty), TyOne (no natty)]
            tm = tup [Abel (no natty), int 5]
        in testShow $ checkEval ty tm
        -- 1
