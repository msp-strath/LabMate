module Lib where

open import Agda.Builtin.Nat public renaming (_+_ to _+N_)
open import Agda.Builtin.String public

record Sg (A : Set)(B : A -> Set) : Set where
 constructor _,_
 field
  fst : A
  snd : B fst

infixr 4 _,_


record One : Set where
 constructor tt

data List (A : Set) : Set where
 [] : List A
 _,-_ : A -> List A -> List A

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] =  []
map f (x ,- xs) = f x ,- map f xs

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

record CdB (T : Nat -> Set) (n : Nat) : Set where
  constructor _^_
  field
   {support} : Nat
   thing : T support
   thinning : support <= n

open CdB public

_^C_ : {n m : Nat}{T : Nat -> Set} -> CdB T n -> n <= m -> CdB T m
(t ^ ph) ^C th = t ^ (ph -< th)

data _+_ (A B : Set) : Set where
 inl : A -> A + B
 inr : B -> A + B

bimap : {A B A' B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
bimap f g (inl x) = inl (f x)
bimap f g (inr x) = inr (g x)

data Bwd (A : Set) : Set where
 [] : Bwd A
 _-,_ : Bwd A -> A -> Bwd A

data Stack (A : Set) : Nat -> Set where
 [] : Stack A 0
 _-,_ : {n : Nat} -> Stack A n -> A -> Stack A (suc n)

module _ {A : Set} where

 only : Stack A 1 -> A
 only (_ -, x) = x

 _<?_ : {n m : Nat} -> n <= m -> Stack A m -> Stack A n
 skip th <? (xz -, x) = th <? xz
 suc th <? (xz -, x) = (th <? xz) -, x
 zero <? _ = []

 _<-_ : {n : Nat} -> 1 <= n -> Stack A n -> A
 th <- xz = only (th <? xz)

 stack : {n : Nat} {B : Set} -> (A -> B) -> Stack A n -> Stack B n
 stack f [] = []
 stack f (xz -, x) = stack f xz -, f x
