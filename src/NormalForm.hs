module NormalForm where

import Data.Bifunctor

import Bwd
import Term

pattern Splus = "plus"
pattern Sone = "one"

pattern Eplus  <- Atom Splus
pattern Eone   <- Atom Sone

pattern Shjux = "hjux"
pattern Svjux = "vjux"

data NFAbel'
 t {- terms -}
 i {- integer multiplicities -}
 = NFAbel
 { nfConst :: i        -- number of *generator* Nils, rendered as an
                       -- integer in terms, i.e., 0 unless Nil is a
                       -- generator
 , nfStuck :: [(t, i)] -- terms should be sorted
 } deriving (Functor, Eq, Show)  -- acts uniformly on multiplicities

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
  (i, [])  -> lit i
  (0, tis) -> go tis
  (i, tis) -> mk Splus (lit i) (go tis)
  where
    go [(tm, i)] = mu i tm
    go ((tm, i) : tis) = mk Splus (mu i tm) (go tis)
    go [] = error "impossible"

    mu 1 = id
    mu i = mk (lit i)

-- termToNFAbel has to be in CoreTT

-- num instance for debugging
instance NATTY n => Num (Term Chk ^ n) where
  s + t = mk Splus s t
  s * t = case s of
   Intg _ -> mk s t
  abs = undefined
  signum = undefined
  fromInteger = lit
  negate = mk (lit (-1 :: Integer))

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


-- TODO : decide how to handle degenerate matrices
type NFMatrix
  h  -- the type of heights of rows (either NFList or NFAbel)
  c  -- the type for singletons/cells (Norm)
  u  -- the type for neutrals
  = [(h, [NFMatrixComponent h c u])]
         -- ^ both the outer and inner lists should be non-empty!

data NFMatrixComponent h c u
  = NFNeutral u
  | NFCell c
  | NFCompound (NFMatrix h c u)
  deriving Show

nfMatrixToTerm
  :: NATTY n
  => NFMatrix h (Norm Chk ^ n) (Norm Syn ^ n)
  -> Norm Chk ^ n
nfMatrixToTerm rows =
  glom (mk Svjux)  $ map (glom (mk Shjux) . map compToTerm . snd) rows
  where
    glom :: (t -> t -> t) -> [t] -> t
    glom _ [] = error "glom: no"
    glom op [t] = t
    glom op (t : ts) = op t $ glom op ts

    compToTerm
      :: NATTY n
      => NFMatrixComponent h (Norm 'Chk ^ n) (Norm 'Syn ^ n) -> Norm 'Chk ^ n
    compToTerm = \case
      NFNeutral t -> E $^ t
      NFCell c -> mk Sone c
      NFCompound m -> nfMatrixToTerm m

vjux :: NFMatrix h c u -> NFMatrix h c u -> NFMatrix h c u
vjux = (++)

hjux :: forall h c u . (Eq h, Monoid h) => NFMatrix h c u -> NFMatrix h c u -> NFMatrix h c u
hjux lrs rrs = post B0  (accum mempty lrs) (accum mempty rrs)
  where
   accum :: forall a. h -> [(h, a)] -> [(h, (h, a))]
   accum d [] = []
   accum d (x@(h, _):xs) = let d' = d <> h in (d', x) : accum d' xs

   post :: Bwd  (h, [NFMatrixComponent h c u])
        -> [(h, (h, [NFMatrixComponent h c u]))]
        -> [(h, (h, [NFMatrixComponent h c u]))]
        -> NFMatrix h c u
   post B0  [] [] = []
   post lrz ((ld, lr) : ldrs) rdrs =
     case break ((ld ==) . fst) rdrs of
       (_, []) -> post (lrz :< lr) ldrs rdrs
       (rdas, (_, rr) : rdrs) -> jux (lrz <>> [lr]) (map snd rdas ++ [rr]) : post B0 ldrs rdrs
   post _ _ _ = error "hjux: no"

   jux :: NFMatrix h c u -> NFMatrix h c u -> (h, [NFMatrixComponent h c u])
   jux [(h, lcs)] [(_, rcs)] = (h, lcs ++ rcs)
   jux [(h, lcs)] r          = (h, lcs ++ [NFCompound r])
   jux l          [(h, rcs)] = (h, NFCompound l : rcs)
   jux l          r          = (foldMap fst l, [NFCompound l, NFCompound r])
