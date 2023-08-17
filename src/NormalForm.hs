module NormalForm where

import Term

pattern Splus = "plus"
pattern Sone = "one"

pattern Eplus  <- Atom Splus
pattern Eone   <- Atom Sone

data NFAbel'
 t {- terms -}
 i {- integer multiplicities -}
 = NFAbel
 { nfConst :: i        -- number of *generator* Nils, rendered as an
                       -- integer in terms, i.e., 0 unless Nil is a
                       -- generator
 , nfStuck :: [(t, i)] -- terms should be sorted
 } deriving (Functor)  -- acts uniformly on multiplicities

-- Integer constants are NFAbel
-- NFAbel is closed under Plus (via merging)
type NFAbel n = NFAbel' (Norm Chk ^ n) Integer

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

nfAbelToTerm :: NATTY n => NFAbel n -> Norm Chk ^ n
nfAbelToTerm NFAbel{..} = case (nfConst, nfStuck) of
  (i, [])  -> int i
  (0, tis) -> go tis
  (i, tis) -> mk Splus (int i) (go tis)
  where
    go [(tm, i)] = mu i tm
    go ((tm, i) : tis) = mk Splus (mu i tm) (go tis)
    go [] = error "impossible"

    mu 1 = id
    mu i = mk (int i)

-- termToNFAbel has to be in CoreTT

-- num instance for debugging
instance NATTY n => Num (Term Chk ^ n) where
  s + t = mk Splus s t
  s * t = case s of
   Intg _ -> mk s t
  abs = undefined
  signum = undefined
  fromInteger = int
  negate = mk (int (-1))

type NFList n =
  [ Either
     (Norm Syn ^ n)  -- stuck list - it is either an embedding or a
                     -- metavariable
     (Norm Chk ^ n)  -- an element
  ]

nfListToTerm :: NATTY n => NFList n -> Norm Chk ^ n
nfListToTerm [] = nil
nfListToTerm (x : xs) = case xs of
  [] -> go x
  _  -> mk Splus (go x) (nfListToTerm xs)
  where
    go (Right tm) = mk Sone tm
    go (Left tm)  = E $^ tm
