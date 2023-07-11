{-# LANGUAGE InstanceSigs #-}
module NormalForm where

import Term

pattern Plus th = A "plus" :^ th
pattern Plus'  <- A "plus" :^ _

pattern Abel th = A "abel" :^ th
pattern Abel'  <- A "abel" :^ _

data NFInteger' t {- terms -}
                i {- integer multiplicities -}
 = NFInteger
 { nfConst :: i        -- number of Nils
 , nfStuck :: [(t, i)] -- terms should be sorted
 } deriving (Functor)  -- acts uniformly on multiplicities

-- Integer constants are NFInteger
-- NFInteger is closed under Plus (via merging)
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
  (i, [])  -> int i
  (0, tis) -> go tis
  (i, tis) -> tup [Plus (no natty), int i, go tis]
  where
    go [(tm, i)] = mu i tm
    go ((tm, i) : tis) = tup [Plus (no natty), mu i tm, go tis]
    go [] = error "impossible"

    mu 1 tm = tm
    mu i tm = tup [int i, tm]

--termToNFInteger has to be in CoreTT


-- for debugging
instance NATTY n => Num (Term ^ n) where
  s + t = tup [Plus (no natty), s, t]
  s * t = case s of
   I i :^ th -> tup [s, t]
  abs = undefined
  signum = undefined
  fromInteger = int
  negate t = tup [ int (-1), t]
