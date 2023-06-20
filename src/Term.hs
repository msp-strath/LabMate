{-# LANGUAGE QuantifiedConstraints #-}
module Term (module Term, module Term.Indexed, module Term.Natty, module Term.Thinning, module Term.Vec) where

import Term.Indexed
import Term.Natty
import Term.Thinning
import Term.Vec
import Hide

data Term :: (Nat -> *) -- representation of metavars
          -> Nat        -- object variable support
          -> *  where
  -- the object var
  V :: Term m (S Z)
  -- atom
  A :: String -> Term m Z
  -- pairing
  P :: Term m l -> Cov l r n -> Term m r -> Term m n
  -- constant function
  K :: Term m n -> Term m n
  -- relevant function
  L :: Hide String -> Term m (S n) -> Term m n
  -- metavar usage
  M :: m k -> Subst m k n -> Term m n

var :: S Z <= n -> Term m ^ n
var = (V :^)

atom :: NATTY n => String -> Term m ^ n
atom s = A s :^ no natty

infixr 5 <&>
(<&>) :: Term m ^ n -> Term m ^ n -> Term m ^ n
(tl :^ th) <&> (tr :^ ph) | u :^ ps <- cop th ph = P tl u tr :^ ps

lam :: String -> Term m ^ S n -> Term m ^ n
lam _ (t :^ No th) = K t :^ th
lam x (t :^ Su th) = L (Hide x) t :^ th

subst :: NATTY n => Vec k (Term m ^ n) -> Subst m k ^ n
subst VN = S0 :^ no natty
subst (tz :# (t :^ ph))
  | sig :^ th <- subst tz
  , u :^ ps <- cop th ph
  = ST sig u t :^ ps

meta :: NATTY n => m k -> Vec k (Term m ^ n) -> Term m ^ n
meta m tz | sig :^ th <- subst tz = M m sig :^ th

tup :: NATTY n => [Term m ^ n] -> Term m ^ n
tup [] = atom ""
tup (t : ts) = t <&> tup ts

data Subst :: (Nat -> *) -- representation of metavars
           -> Nat        -- src scope
           -> Nat        -- tgt support
           -> * where
  S0 :: Subst m Z Z
  ST :: Subst m k l -> Cov l r n -> Term m r -> Subst m (S k) n

substSrc :: Subst m k n -> Natty k
substSrc S0 = Zy
substSrc (ST sig _ _) = Sy (substSrc sig)

substSupport :: Subst m k n -> Natty n
substSupport S0 = Zy
substSupport (ST _ u _) = bigEnd (covl u)

tmShow :: forall m n .
          (forall i . Show (m i))
       => Bool         -- is the term a cdr
       -> Term m ^ n
       -> Vec n String -- we know the names of all vars in scope
       -> String
tmShow b (V :^ th) ctx = barIf b ++ vonly (th ?^ ctx)
tmShow b (A "" :^ _) _
  | b = ""
  | otherwise = "[]"
tmShow b (A s :^ _)  _ = barIf b ++ "'" ++ s
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
    substShow :: forall j n . Subst m j ^ n -> Vec n String -> String
    substShow (S0 :^ _) _ = ""
    substShow (ST sig u t :^ th) ctx = concat [substShow (sig :^ covl u -< th) ctx, tmShow False (t :^ covr u -< th) ctx, ", "]

barIf :: Bool -> String
barIf True = " | "
barIf False = ""

data Roof :: (Nat -> *) -> Nat -> Nat -> Nat -> * where
  Roof :: Subst m l l' -> Cov l' r' n -> Subst m r r' -> Roof m l r n

roofLemma :: Cov l r k -> Subst m k n -> Roof m l r n
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

idSubstEh :: Subst m k n -> Either (Positive k) (k == n)
idSubstEh S0 = Right Refl
idSubstEh (ST sig (NS u) V) | Refl <- allRight (swapCov u) = case idSubstEh sig of
  Left (IsSy n) -> Left $ IsSy (Sy n)
  Right Refl -> Right Refl
idSubstEh (ST sig _ _) = Left (IsSy (substSrc sig))

class Substable (t :: Nat -> *) where
  type MetaOf t :: Nat -> *

  (//) :: t k -> Subst (MetaOf t) k n -> t n
  t // sig = case idSubstEh sig of
    Left (IsSy _) -> t /// sig
    Right Refl -> t

  -- substWorker
  (///) :: t (S k)
        -> Subst (MetaOf t) (S k) n -- must not be the id subst
        -> t n

instance Substable (Term m) where
  type MetaOf (Term m) = m

  V /// ST S0 u t | Refl <- allRight u = t
  P tl u tr /// sig | Roof sigl u' sigr <- roofLemma u sig =
    P (tl // sigl) u' (tr // sigr)
  K t /// sig = K (t /// sig)
  L x t /// sig = L x (t /// ST sig (NS (lCov (substSupport sig))) V)
  M m tau /// sig = M m (tau /// sig)

instance Substable (Subst m k) where
  type MetaOf (Subst m k) = m

  ST tau u t /// sig
    | Roof sigl u' sigr <- roofLemma u sig = ST (tau // sigl) u' (t // sigr)

theTerm :: Term (Konst String) ^ S (S (S Z))
theTerm = lam "w" $ tup [var 0, var 1, var 2]
  --meta (Konst "m") (atom <$> theCtx)
  --lam "x" $ var 0

theCtx :: Vec (S (S (S Z))) String
theCtx = VN :# "z" :# "y" :# "x"
