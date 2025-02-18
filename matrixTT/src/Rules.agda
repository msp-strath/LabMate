{-# OPTIONS --rewriting #-}
module Rules where

open import Lib
open import Model

data Term (sc : Nat) : Set where
  var  : 1 <= sc -> Term sc
  atom : Atom -> Term sc
  pair : Term sc -> Term sc -> Term sc
  bind : Term (suc sc) -> Term sc
  elim : Term sc -> Term sc -> Term sc

pattern nil = atom ""

mutual
-- magic version

 data _|-TYPE_ {sc : Nat} (Ga : Context sc) : Term sc -> Set where
   one : Ga |-TYPE (pair (atom "One") nil)
   list : {a : Term sc} -> Ga |-TYPE a -> Ga |-TYPE pair (atom "List") (pair a nil)
   pi : {a : Term sc} {b : Term (suc sc)}
      -> (aOk : Ga |-TYPE a)
      -> (Ga , λ γ →  [ aOk ]TYPE γ ) |-TYPE b
      -> Ga |-TYPE (pair (atom "Pi") (pair a (pair (bind b) nil)))


 [_]TYPE : {sc sc' : Nat} {Ga : Context sc} {ty : Term sc}
         ->  Ga |-TYPE ty -> Env sc' Ga -> Type sc'
 [ one ]TYPE _ = one
 [ list a ]TYPE rho = list ([ a ]TYPE rho)
 [_]TYPE {sc' = sc'} {Ga} (pi a b) rho  =
  pi ([ a ]TYPE rho) λ th x -> [ b ]TYPE (_ , no , rho , th , subst (λ z → El' ([ a ]TYPE z) th) (cong (λ z → subst (El' ∣ Ga ∣) z rho) (sym no-unique-no)) x , sym (no-unique (no -< th)))
