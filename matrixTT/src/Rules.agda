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
   sg : {a : Term sc} {b : Term (suc sc)}
      -> (aOk : Ga |-TYPE a)
      -> (Ga , λ γ →  [ aOk ]TYPE γ ) |-TYPE b
      -> Ga |-TYPE (pair (atom "Sg") (pair a (pair (bind b) nil)))
   -- ne : (1 <= sc)

 [_]TYPE : {sc sc' : Nat} {Ga : Context sc} {ty : Term sc}
         ->  Ga |-TYPE ty -> Env sc' Ga -> Type sc'
 [ one ]TYPE _ = one
 [ list a ]TYPE rho = list ([ a ]TYPE rho)
 [_]TYPE {sc' = sc'} {Ga} (pi a b) rho  =
  pi ([ a ]TYPE rho) λ th x -> [ b ]TYPE (_ , no , rho , th , x , sym (no-unique (no -< th)))
 [_]TYPE {sc' = sc'} {Ga} (sg a b) rho  =
  sg ([ a ]TYPE rho) λ th x -> [ b ]TYPE (_ , no , rho , th , x , sym (no-unique (no -< th)))

mutual
 data  _|-_::_ {sc : Nat} (Ga : Context sc) : Term sc -> Type sc -> Set where
   void : Ga |- nil :: one
   empty : {A : Type sc} -> Ga |- nil :: list A
   sing : {A : Type sc} -> {t : Term sc} -> Ga |- t :: A -> Ga |-(pair (atom "sing") (pair t nil)) :: list A
   append : {A : Type sc} -> {ts : Term sc} -> {ts' : Term sc}
          -> Ga |- ts :: list A -> Ga |- ts' :: list A
          -> Ga |-(pair (atom "plus") (pair ts (pair ts' nil))) :: list A
   dpair : {A : Type sc} -> {B : {sc' : Nat} -> (th : sc <= sc') -> El (A ^ th) -> Type sc'} -> {s : Term sc} -> {t : Term sc}
         -> (j : Ga |- s :: A)
         -> Ga |- t :: B io [ j ]TERM
         -> Ga |- pair s t :: sg A B
   lam : {A : Type sc} -> {B : {sc' : Nat} -> (th : sc <= sc') -> El (A ^ th) -> Type sc'} -> {t : Term (suc sc)}
         -> (Ga , λ x → {!!}) |- t :: B (skip io) (unquoteEl A (skip io) (neutral (suc no) []))
         -> Ga |- pair (atom "lam") (pair (bind t) nil) :: pi A B

 [_]TERM : {sc : Nat} {Ga : Context sc} {t : Term sc} {A : Type sc} -> Ga |- t :: A -> El (A ^ io)
 --  we are not getting away with evaluating just at `io` -------------------------------------^
 [ void ]TERM = tt
 [ empty ]TERM = []
 [ sing j ]TERM = inr  [ j ]TERM ,- []
 [ append j j' ]TERM =  [ j ]TERM ++ [ j' ]TERM
 [ dpair j j' ]TERM = _ , io , [ j ]TERM , io , [ j' ]TERM , refl


{-
 data  _|-_∶_ {sc : Nat} (Ga : Context sc) : Term sc -> Term sc -> Set where
   tt : Ga |- nil ∶ (pair (atom "One") nil)
   [] : {a : Term sc} -> Ga |-TYPE a -> Ga |- nil ∶ pair (atom "List") (pair a nil)
   _∷_ : {a : Term sc} {x xs : Term sc}
        -> Ga |-TYPE a
        -> Ga |- x ∶ a -> Ga |- xs ∶ pair (atom "List") (pair a nil)
        -> Ga |- pair x (pair xs nil) ∶ pair (atom "List") (pair a nil)
   lam : {a : Term sc} {b : Term (suc sc)}
         -> (t : Term (suc sc))
         -> (aOk : Ga |-TYPE a)
         -> (bOk : (Ga , λ γ -> [ aOk ]TYPE γ) |-TYPE b)
         -> (Ga , λ γ -> [ aOk ]TYPE γ) |- t ∶ b
         -> Ga |- bind t ∶ (pair (atom "Pi") (pair a (pair (bind b) nil)))
   pair : {a : Term sc} {b : Term (suc sc)}
        -> (s : Term sc) -> (t : Term sc)
        -> (aOk : Ga |-TYPE a)
        -> (bOk : (Ga , λ γ -> [ aOk ]TYPE γ) |-TYPE b)
        -> Ga |- s ∶ a
        -> Ga |- t ∶ {!!}
        -> Ga |- pair s t ∶(pair (atom "Sg") (pair a (pair (bind b) nil)))
-}

   {- [_]TERM : {sc : Nat}{Ga : Context sc}{x : Term sc}
           -> Ga |- x ∶ t -> Env sc Ga -> -}
