module Term (module Term, module Term.Indexed, module Term.Natty, module Term.Thinning, module Term.Vec) where

import Term.Indexed
import Term.Natty
import Term.Thinning
import Term.Vec

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
  L :: Term m (S n) -> Term m n
  -- metavar usage
  M :: m k -> Subst m k n -> Term m n

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

class Substable (t :: Nat -> *) where
  type MetaOf t :: Nat -> *
  (//) :: t k -> Subst (MetaOf t) k n -> t n

instance Substable (Term m) where
  type MetaOf (Term m) = m
  V // ST S0 u t | Refl <- allRight u = t
  A s // S0 = A s
  P tl u tr // sig | Roof sigl u' sigr <- roofLemma u sig =
    P (tl // sigl) u' (tr // sigr)
  K t // sig = K (t // sig)
  L t // sig = L (t // ST sig (NS (lCov (substSupport sig))) V)
  M m tau // sig = M m (tau // sig)

instance Substable (Subst m k) where
  type MetaOf (Subst m k) = m
  S0 // S0 = S0
  ST tau u t // sig
    | Roof sigl u' sigr <- roofLemma u sig = ST (tau // sigl) u' (t // sigr)
