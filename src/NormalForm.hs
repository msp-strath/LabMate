module NormalForm where

import Term

pattern Splus = "plus"
pattern Sone = "one"

pattern Plus th = A Splus :^ th
pattern Plus'  <- A Splus :^ _

pattern One th = A Sone :^ th
pattern One'  <- A Sone :^ _

data NFAbel'
 t {- terms -}
 i {- integer multiplicities -}
 = NFAbel
 { nfConst :: i        -- number of Nils
 , nfStuck :: [(t, i)] -- terms should be sorted
 } deriving (Functor)  -- acts uniformly on multiplicities

-- Integer constants are NFAbel
-- NFAbel is closed under Plus (via merging)
type NFAbel n = NFAbel' (Term ^ n) Integer

instance (Ord t, Num i, Eq i) => Semigroup (NFAbel' t i) where
  (<>) = mappend

instance (Ord t, Num i, Eq i) => Monoid (NFAbel' t i) where
  mempty = NFAbel {nfConst = 0, nfStuck = []}
  NFAbel x xtis `mappend` NFAbel y ytis = NFAbel
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

nfAbelToTerm :: NATTY n => NFAbel n -> Term ^ n
nfAbelToTerm NFAbel{..} = case (nfConst, nfStuck) of
  (i, [])  -> int i
  (0, tis) -> go tis
  (i, tis) -> tup [Plus (no natty), int i, go tis]
  where
    go [(tm, i)] = mu i tm
    go ((tm, i) : tis) = tup [Plus (no natty), mu i tm, go tis]
    go [] = error "impossible"

    mu 1 tm = tm
    mu i tm = tup [int i, tm]

-- termToNFAbel has to be in CoreTT

-- num instance for debugging
instance NATTY n => Num (Term ^ n) where
  s + t = tup [Plus (no natty), s, t]
  s * t = case s of
   I i :^ th -> tup [s, t]
  abs = undefined
  signum = undefined
  fromInteger = int
  negate t = tup [ int (-1), t]

type NFList n =
  [( Term ^ n
   , Bool -- `True` means an element, `False` a stuck list
   )]

nfListToTerm :: NATTY n => NFList n -> Term ^ n
nfListToTerm [] = Nil
nfListToTerm (x : xs) = case xs of
  [] -> go x
  _  -> tup [Plus (no natty), go x, nfListToTerm xs]
  where
    go (tm, True) = tup [One (no natty), tm]
    go (tm, False) = tm
