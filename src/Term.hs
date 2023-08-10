{-# LANGUAGE QuantifiedConstraints #-}
module Term (module Term
            , module Term.Indexed
            , module Term.Natty
            , module Term.Thinning
            , module Term.Vec) where
import Term.Indexed
import Term.Natty
import Term.Thinning
import Term.Vec
import Hide

type Name = String

data Term (n :: Nat) where       -- object variable support
  -- the object var
  V :: Term (S Z)
  -- atom
  A :: String -> Term Z
  -- integer constants
  I :: Integer -> Term Z
  -- pairing
  P :: Term l -> Cov l r n -> Term r -> Term n
  -- constant function
  K :: Term n -> Term n
  -- relevant function
  L :: Hide String -> Term (S n) -> Term n
  -- metavar usage
  M :: (Name, Natty k) -> Subst k n -> Term n

-- for documentary purposes; used only when we *know* (and not merely
-- hope) a term is a type and a normalised type, respectively
type Type = Term
type NmTy = Type

instance Eq (Term n) where
  t == t' = compare t t' == EQ

instance Ord (Term n) where
  compare  V         V       = EQ
  compare (A s)     (A s')   = compare s s'
  compare (I n)     (I n')   = compare n n'
  compare (P l u r) (P l' u' r') = case cmpCov u u' of
    LT' -> LT
    GT' -> GT
    EQ' (Refl, Refl) -> compare (l', r') (l', r')
  compare (K t)         (K t')   = compare t t'
  compare (L _ t)       (L _ t') = compare t t'
  compare (M (s, k) su) (M (s', k') su') = case cmpNatty k k' of
    LT' -> LT
    GT' -> GT
    EQ' Refl -> compare (s, su) (s', su')

  compare t1 t2 = compare (helper t1) (helper t2)
   where
      helper :: Term n -> Integer
      helper = \case
        { V{} -> 0; A{} -> 1; I{} -> 2; P{} -> 3
        ; K{} -> 4; L{} -> 5; M{} -> 6 }

--------------- smart ctors ---------------
var :: S Z <= n -> Term ^ n
var = (V :^)

atom :: NATTY n => String -> Term ^ n
atom s = A s :^ no natty

pattern At :: NATTY n => String -> Term ^ n
pattern At s <- A s :^ _
  where At s = atom s

nil :: NATTY n => Term ^ n
nil = atom ""

nilEh :: Term ^ n -> Maybe ()
nilEh (A "" :^ _) = Just ()
nilEh _ = Nothing

pattern Nil :: NATTY n => Term ^ n
pattern Nil <- A "" :^ _
  where Nil = nil

int :: NATTY n => Integer -> Term ^ n
int i = I i :^ no natty

infixr 5 <&>
(<&>) :: Term ^ n -> Term ^ n -> Term ^ n
(tl :^ th) <&> (tr :^ ph) | u :^ ps <- cop th ph = P tl u tr :^ ps

pairEh :: Term ^ n -> Maybe (Term ^ n, Term ^ n)
pairEh (P tl u tr :^ ph) = Just (tl :^ covl u -< ph, tr :^ covr u -< ph)
pairEh _ = Nothing

lam :: String -> Term ^ S n -> Term ^ n
lam _ (t :^ No th) = K t :^ th
lam x (t :^ Su th) = L (Hide x) t :^ th

lamEh :: Term ^ n -> Maybe (Term ^ S n)
lamEh (K t :^ th) = Just (t :^ No th)
lamEh (L _ t :^ th) = Just (t :^ Su th)
lamEh _ = Nothing

lamNameEh :: Term ^ n -> Maybe (String, Term ^ S n)
lamNameEh (K t :^ th) = Just ("_", t :^ No th)
lamNameEh (L (Hide x) t :^ th) = Just (x, t :^ Su th)
lamNameEh _ = Nothing

subst :: NATTY n => Vec k (Term ^ n) -> Subst k ^ n
subst VN = S0 :^ no natty
subst (tz :# (t :^ ph))
  | sig :^ th <- subst tz
  , u :^ ps <- cop th ph
  = ST sig u t :^ ps

meta :: NATTY n => (Name, Natty k) -> Vec k (Term ^ n) -> Term ^ n
meta m tz | sig :^ th <- subst tz = M m sig :^ th

tup :: NATTY n => [Term ^ n] -> Term ^ n
tup = foldr (<&>) (atom "")

tupEh :: Term ^ n -> Maybe [Term ^ n]
tupEh t | Just () <- nilEh t = Just []
tupEh t = do
  (h, t) <- pairEh t
  (h :) <$> tupEh t

type Tag = String

tag :: NATTY n => Tag -> [Term ^ n] -> Term ^ n
tag s ts = tup $ atom s : ts

tagEh :: Term ^ n -> Maybe (Tag, [Term ^ n])
tagEh (A s@(_:_) :^ _) = Just (s, [])
tagEh t = case tupEh t of
  Just ((A s@(_:_) :^ _):ts) -> Just (s, ts)
  _   -> Nothing

-------------------------------------------

data Subst (srcScope :: Nat) (tgtSupport :: Nat) where
  S0 :: Subst Z Z
  ST :: Subst k l -> Cov l r n -> Term r -> Subst (S k) n

substSrc :: Subst k n -> Natty k
substSrc S0 = Zy
substSrc (ST sig _ _) = Sy (substSrc sig)

substSupport :: Subst k n -> Natty n
substSupport S0 = Zy
substSupport (ST _ u _) = bigEnd (covl u)

sub0 :: Term ^ n -> Subst (S n) ^ n
sub0 (tm :^ th) = let n = bigEnd th
  in ST (idSubst n) (leftAll th) tm :^ io n

tmShow :: forall n
       .  Bool         -- is the term a cdr
       -> Term ^ n
       -> Vec n String -- we know the names of all vars in scope
       -> String
tmShow b (V :^ th) ctx = barIf b ++ vonly (th ?^ ctx)
tmShow b (A "" :^ _) _
  | b = ""
  | otherwise = "[]"
tmShow b (A s :^ _) _ = barIf b ++ "'" ++ s
tmShow b (I i :^ _) _ = barIf b ++ show i
tmShow b (P tl u tr :^ th) ctx =
  if b then " " ++ s else "[" ++ s ++ "]"
  where
    s = tmShow False (tl :^ covl u -< th) ctx ++ tmShow True (tr :^ covr u -< th) ctx
tmShow b (K tm :^ th) ctx = barIf b ++ "(\\_. " ++ tmShow b (tm :^ th) ctx ++ ")"
tmShow b (L (Hide nm) tm :^ th) ctx = concat [barIf b, "(\\", x, ". ", tmShow False (tm :^ Su th) (ctx :# x), ")"]
  where
    x = head $ filter (not . (`elem` ctx)) (nm : [nm ++ show i | i <- [0..]])
tmShow b (M m sig :^ th) ctx = barIf b ++ show m ++ case idSubstEh sig of
  Left (IsSy n) -> case sig of
    ST sig u t -> concat ["{", substShow (sig :^ covl u -< th) ctx, tmShow False (t :^ covr u -< th) ctx, "}"]
  Right Refl -> ""
  where
    substShow :: forall j n . Subst j ^ n -> Vec n String -> String
    substShow (S0 :^ _) _ = ""
    substShow (ST sig u t :^ th) ctx = concat [substShow (sig :^ covl u -< th) ctx, tmShow False (t :^ covr u -< th) ctx, ", "]

barIf :: Bool -> String
barIf True = " | "
barIf False = ""

data Roof ::  Nat -> Nat -> Nat -> * where
  Roof :: Subst l l' -> Cov l' r' n -> Subst r r' -> Roof l r n

roofLemma :: Cov l r k -> Subst k n -> Roof l r n
roofLemma ZZ S0 = Roof S0 ZZ S0
roofLemma (SN u0) (ST sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , u3 :^\^: u4 <- rotateRCov (swapCov u2) u1
  = Roof (ST sigl u4 t) (swapCov u3) sigr
roofLemma (NS u0) (ST sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , u3 :^\^: u4 <- rotateRCov u2 u1
  = Roof sigl u3 (ST sigr u4 t)
roofLemma (SS u0) (ST sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , MiddleFour u3 u4 u5 <- middleFour u2 u1 (allCov (weeEnd (covr u1)))
  = Roof (ST sigl u3 t) u4 (ST sigr u5 t)

idSubst :: Natty n -> Subst n n
idSubst Zy  = S0
idSubst (Sy n) = ST (idSubst n) (NS (lCov n)) V

idSubstEh :: Subst k n -> Either (Positive k) (k == n)
idSubstEh S0 = Right Refl
idSubstEh (ST sig (NS u) V) | Refl <- allRight (swapCov u) = case idSubstEh sig of
  Left (IsSy n) -> Left $ IsSy (Sy n)
  Right Refl -> Right Refl
idSubstEh (ST sig _ _) = Left (IsSy (substSrc sig))

instance Eq (Subst k n) where
  s == t = compare s t == EQ

instance Ord (Subst k n) where
  compare S0 S0 = EQ
  compare (ST sig u t) (ST sig' u' t') = case cmpCov u u' of
    LT' -> LT
    GT' -> GT
    EQ' (Refl, Refl) -> compare (sig, t) (sig', t')

class Substable (t :: Nat -> *) where

  (//) :: t k -> Subst k n -> t n
  t // sig = case idSubstEh sig of
    Left (IsSy _) -> t /// sig
    Right Refl -> t

  -- substWorker
  (///) :: t (S k)
        -> Subst (S k) n -- must not be the id subst
        -> t n

instance Substable Term where

  V /// ST S0 u t | Refl <- allRight u = t
  P tl u tr /// sig | Roof sigl u' sigr <- roofLemma u sig =
    P (tl // sigl) u' (tr // sigr)
  K t /// sig = K (t /// sig)
  L x t /// sig = L x (t /// ST sig (NS (lCov (substSupport sig))) V)
  M m tau /// sig = M m (tau /// sig)

instance Substable (Subst k) where
  ST tau u t /// sig
    | Roof sigl u' sigr <- roofLemma u sig = ST (tau // sigl) u' (t // sigr)

(//^) :: Term ^ k -> Subst k ^ n -> Term ^ n
(t :^ th) //^ (sig :^ ph) | Roof sigl u sigr <- roofLemma (rightAll th) sig =
  t // sigl :^ covl u -< ph


theTerm :: Term ^ S (S (S Z))
theTerm = lam "w" $ tup [var 0, var 2, var 3]
  --meta (Konst "m") (atom <$> theCtx)
  --lam "x" $ var 0

theSubst :: Subst ('S ('S ('S 'Z))) ^ S (S (S Z))
theSubst = subst $ VN :# var 1 :# var 0 :# var 2

theCtx :: Vec (S (S (S Z))) String
theCtx = VN :# "z" :# "y" :# "x"

testShow :: Term ^ S (S (S Z)) -> IO ()
testShow t = putStrLn (tmShow False t theCtx)
