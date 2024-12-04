module Lib where

open import Agda.Builtin.Nat public renaming (_+_ to _+N_)
open import Agda.Builtin.String public

record Sg (A : Set)(B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

record One : Set where
 constructor tt

data List (A : Set) : Set where
 [] : List A
 _,-_ : A -> List A -> List A

data _<=_ : Nat -> Nat -> Set where
 skip : ∀ {n m} -> n <= m ->     n <= suc m
 suc  : ∀ {n m} -> n <= m -> suc n <= suc m
 zero : zero <= zero

io : {n : Nat} -> n <= n
io {zero} = zero
io {suc n} = suc (io {n})

no : {n : Nat} -> zero <= n
no {zero} = zero
no {suc n} = skip (no {n})

_-<_ : {l n m : Nat} -> l <= n -> n <= m -> l <= m
ph -< skip th = skip (ph -< th)
skip ph -< suc th = skip (ph -< th)
suc ph -< suc th = suc (ph -< th)
ph -< zero = ph

data _+_ (A B : Set) : Set where
 inl : A -> A + B
 inr : B -> A + B

data Bwd (A : Set) : Set where
 [] : Bwd A
 _-,_ : Bwd A -> A -> Bwd A
