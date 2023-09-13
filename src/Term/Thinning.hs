{-# LANGUAGE QuantifiedConstraints #-}
module Term.Thinning where

import Term.Indexed
import Term.Natty

-- thinnings
data (<=) :: Nat -> Nat -> * where
  No :: n <= m ->   n <= S m
  Su :: n <= m -> S n <= S m
  Ze ::             Z <= Z

instance Show (n <= m) where
  show th = help th "]" where
    help :: forall n m. n <= m -> String -> String
    help (No th) s = help th ('0' : s)
    help (Su th) s = help th ('1' : s)
    help  Ze     s = '[' : s

-- compute singleton for the big end
bigEnd :: n <= m -> Natty m
bigEnd (No th) = Sy (bigEnd th)
bigEnd (Su th) = Sy (bigEnd th)
bigEnd  Ze     = Zy

-- ... and the wee end
weeEnd :: n <= m -> Natty n
weeEnd (No th) = weeEnd th
weeEnd (Su th) = Sy (weeEnd th)
weeEnd  Ze     = Zy

thinEqEh :: k <= l -> n <= m -> Maybe (k == n, l == m)
thinEqEh (No th) (No ph) = do { (Refl, Refl) <- thinEqEh th ph ; pure (Refl, Refl) }
thinEqEh (Su th) (Su ph) = do { (Refl, Refl) <- thinEqEh th ph ; pure (Refl, Refl) }
thinEqEh  Ze      Ze     =                                       pure (Refl, Refl)
thinEqEh  _       _      = Nothing

cmpThin :: k <= m -> n <= m -> Ordering' (k == n)
cmpThin (No th) (Su ph) = LT'
cmpThin (Su th) (No ph) = GT'
cmpThin (No th) (No ph) = cmpThin th ph
cmpThin (Su th) (Su ph) = case cmpThin th ph of
  LT' -> LT'
  EQ' Refl -> EQ' Refl
  GT' -> GT'
cmpThin  Ze      Ze     = EQ' Refl

-- identity for thinnings
io :: forall m. Natty m -> m <= m
io (Sy n) = Su (io n)
io  Zy    = Ze

-- action of thinnings
class Thinny (f :: Nat -> *) where
  (-<) :: forall n m. f n -> n <= m -> f m

-- composition is the action of thinnings on thinnings
instance Thinny ((<=) l) where
  th    -< No ph = No (th -< ph)
  No th -< Su ph = No (th -< ph)
  Su th -< Su ph = Su (th -< ph)
  Ze    -< Ze    = Ze

-- the empty thinning
no :: forall m. Natty m -> Z <= m
no (Sy m) = No (no m)
no  Zy    = Ze

-- `Cov l r m` codes up `l <= m` and `r <= m`, such that
-- `m` is covered
data Cov :: Nat -> Nat -> Nat -> * where
  SN :: Cov l r m -> Cov (S l)    r  (S m)
  NS :: Cov l r m -> Cov    l  (S r) (S m)
  SS :: Cov l r m -> Cov (S l) (S r) (S m)
  ZZ ::              Cov  Z     Z     Z

instance Show (Cov l r m) where
  show u = help u "]" where
    help :: forall l r m. Cov l r m -> String -> String
    help (SN u) s = help u ("10." ++ s)
    help (NS u) s = help u ("01." ++ s)
    help (SS u) s = help u ("11." ++ s)
    help ZZ     s = "[" ++ s

-- extract the left thinning
covl :: Cov l r m -> l <= m
covl (SN u) = Su (covl u)
covl (NS u) = No (covl u)
covl (SS u) = Su (covl u)
covl  ZZ    = Ze

-- ... and the right one as well
covr :: Cov l r m -> r <= m
covr (SN u) = No (covr u)
covr (NS u) = Su (covr u)
covr (SS u) = Su (covr u)
covr  ZZ    = Ze

cmpCov :: Cov l r n -> Cov l' r' n -> Ordering' (l == l', r == r')
cmpCov u u' = case cmpThin (covl u) (covl u') of
  LT' -> LT'
  GT' -> GT'
  EQ' q -> case cmpThin (covr u) (covr u') of
    LT' -> LT'
    EQ' q' -> EQ' (q, q')
    GT' -> GT'

-- CoDeBruijn pairing of a thing with its thinning
-- `n` is implicitly existential
data (^) :: (Nat -> *) -> Nat -> * where
  (:^) :: p n -> n <= m -> p ^ m


scopeOf :: p ^ n -> Natty n
scopeOf (_ :^ th) = bigEnd th

-- (^) is the free Thinny on (p :: Nat -> *)
instance Thinny ((^) (p :: Nat -> *)) where
  (p :^ th) -< ph = p :^ (th -< ph)

instance (forall (n :: Nat). Eq (p n)) => Eq (p ^ m) where
  (p :^ th) == (q :^ ph) = case cmpThin th ph of
    EQ' Refl -> p == q
    _ -> False

instance (forall (n :: Nat). Ord (p n)) => Ord (p ^ m) where
  compare (p :^ th) (q :^ ph) = case cmpThin th ph of
    LT' -> LT
    GT' -> GT
    EQ' Refl -> compare p q

wk :: p ^ n -> p ^ S n
wk (p :^ th) = p :^ No th -- faster than composition

-- coproduct diagrams in (<= m) with the existential witness
-- and its thinning being coproduct object
type Cop l r m = Cov l r ^ m

-- computes the union `n` of two subsets, its inclusion map,
-- as well as the inclusions into `n`
cop :: l <= m -> r <= m -> Cop l r m
cop (No th) (No ph) = case cop th ph of u :^ ps ->    u :^ No ps
cop (No th) (Su ph) = case cop th ph of u :^ ps -> NS u :^ Su ps
cop (Su th) (No ph) = case cop th ph of u :^ ps -> SN u :^ Su ps
cop (Su th) (Su ph) = case cop th ph of u :^ ps -> SS u :^ Su ps
cop  Ze      Ze     =                              ZZ   :^ Ze

allRight :: Cov Z r n -> r == n
allRight ZZ = Refl
allRight (NS u) | Refl <- allRight u = Refl

rightAll :: n <= m -> Cov n m m
rightAll (No th) = NS $ rightAll th
rightAll (Su th) = SS $ rightAll th
rightAll Ze      = ZZ

leftAll :: n <= m -> Cov m n m
leftAll = swapCov . rightAll

lCov :: Natty l -> Cov l Z l
lCov Zy = ZZ
lCov (Sy l) = SN (lCov l)

swapCov :: Cov l r m -> Cov r l m
swapCov ZZ = ZZ
swapCov (NS u) = SN (swapCov u)
swapCov (SN u) = NS (swapCov u)
swapCov (SS u) = SS (swapCov u)

data IUJK :: Nat -> Nat -> Nat -> Nat -> * where
  (:^\^:) :: Cov i jk ijk -> Cov j k jk -> IUJK i j k ijk

data IJUK :: Nat -> Nat -> Nat -> Nat -> * where
  (:^/^:) :: Cov i j ij -> Cov ij k ijk -> IJUK i j k ijk

data MiddleFour :: Nat -> Nat -> Nat -> Nat -> Nat -> * where
  MiddleFour :: Cov a c ac -> Cov ac bd abcd -> Cov b d bd
             -> MiddleFour a b c d abcd

rotateRCov :: Cov i j ij -> Cov ij k ijk -> IUJK i j k ijk
rotateRCov ZZ ZZ = ZZ :^\^: ZZ
rotateRCov iuj (NS ijuk) | iujk :^\^: juk  <- rotateRCov iuj ijuk =
 NS iujk :^\^: NS juk
rotateRCov (SN iuj) (SN ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 SN iujk :^\^: juk
rotateRCov (NS iuj) (SN ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 NS iujk :^\^: SN juk
rotateRCov (SS iuj) (SN ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 SS iujk :^\^: SN juk
rotateRCov (SN iuj) (SS ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 SS iujk :^\^: NS juk
rotateRCov (NS iuj) (SS ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 NS iujk :^\^: SS juk
rotateRCov (SS iuj) (SS ijuk) | iujk :^\^: juk <- rotateRCov iuj ijuk =
 SS iujk :^\^: SS juk

rotateLCov :: Cov i jk ijk -> Cov j k jk -> IJUK i j k ijk
rotateLCov iujk juk | kuji :^\^: jui <- rotateRCov (swapCov juk) (swapCov iujk)
 = swapCov jui :^/^: swapCov kuji

allCov :: Natty n -> Cov n n n
allCov Zy = ZZ
allCov (Sy n) = SS (allCov n)

middleFour :: Cov a b ab -> Cov ab cd abcd -> Cov c d cd -> MiddleFour a b c d abcd
middleFour aub abucd cud
  | aubcd :^\^: bucd  <- rotateRCov aub abucd
  , buc   :^/^: bcud  <- rotateLCov bucd cud
  , cub               <- swapCov buc
  , cubd  :^\^: bud   <- rotateRCov cub bcud
  , auc   :^/^: acubd <- rotateLCov aubcd cubd
  = MiddleFour auc acubd bud
{-
-- relevant pairing
data (&) :: (Nat -> *) -> (Nat -> *) -> (Nat -> *) where
  P :: s l -> Cov l r m -> t r -> (s & t) m

-- smart constructor (for CoDeBruijn RP)
(^&^) :: s ^ m -> t ^ m -> (s & t) ^ m
(s :^ th) ^&^ (t :^ ph) = case cop th ph of u :^ ps -> P s u t :^ ps
-}

{-
-- binding
data B :: (Nat -> *) -> Nat -> * where
  K :: p n     -> B p n  -- vacuous
  L :: p (S n) -> B p n  -- relevant

-- smart constructor
bi :: p ^ S n -> B p ^ n
bi (p :^ No th) = K p :^ th
bi (p :^ Su th) = L p :^ th
-}

-- spans in (<=)
data Span :: Nat -> Nat -> Nat -> * where
  Span :: n <= l -> n <= r -> Span l r n

-- products in (<=m), a.k.a pullbacks in (<=),
-- a.k.a intersection of subsets
type Pub l r m = Span l r ^ m

-- existential witness
pub :: l <= m -> r <= m -> Pub l r m
--   x       y                                   x & y
pub (No th) (No ph) = case pub th ph of
  Span th' ph' :^ ps' -> Span     th'      ph'  :^ No ps'
pub (No th) (Su ph) = case pub th ph of
  Span th' ph' :^ ps' -> Span     th'  (No ph') :^ No ps'
pub (Su th) (No ph) = case pub th ph of
  Span th' ph' :^ ps' -> Span (No th')     ph'  :^ No ps'
pub (Su th) (Su ph) = case pub th ph of
  Span th' ph' :^ ps' -> Span (Su th') (Su ph') :^ Su ps'
pub  Ze      Ze     =    Span  Ze       Ze      :^ Ze

-- testing if one subset is included in another by checking
-- if the pullback is degenerate
thicken :: l <= m -> n <= m -> Maybe (l <= n)
thicken th ph = case pub th ph of
  Span th' ph' :^ ps' -> do
    (Refl, Refl) <- thinEqEh th' (io $ weeEnd th)
    pure ph'

-- (<=) are monoidal cat wrt AddR
thAdd :: AddR a b c -> a <= d -> b <= e -> AddR d e f -> c <= f
thAdd abc ad (No be) (AddS def) = No (thAdd abc ad be def)
thAdd (AddS abc) ad (Su be) (AddS def) = Su (thAdd abc ad be def)
thAdd (AddZ _) ad Ze (AddZ _) = ad

instance NATTY n => Num (S Z <= n) where
  fromInteger i = go i n
    where
      n = natty
      go :: forall n. Integer -> Natty n -> S Z <= n
      go 0 (Sy n) = Su $ no n
      go i (Sy n) = No $ go (i - 1) n
      go _ _ = error $ "DeBruijn idx out of bounds: " ++ show i ++ " <= " ++ show n ++ "."
  (+) = undefined
  (*) = undefined
  (-) = undefined
  abs = undefined
  signum = undefined
