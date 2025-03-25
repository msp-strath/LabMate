{-# OPTIONS --rewriting #-}
module Lib where

open import Agda.Builtin.Nat public renaming (_+_ to _+N_)
open import Agda.Builtin.String public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set}
     -> (f : A -> B) -> {a a' : A} -> a ≡ a' -> f a ≡ f a'
cong f refl = refl

cong2 : {A B C : Set}
     -> (f : A -> B → C)
     -> {a a' : A} -> a ≡ a'
     -> {b b' : B} → b ≡ b'
     -> f a b ≡ f a' b'
cong2 f refl refl = refl


subst : {A : Set}(P : A → Set) {x y : A}
      -> x ≡ y -> P x -> P y
subst P refl px = px

subst2 : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
      -> {a a' : A} -> (aq : a ≡ a')
      -> {b : B a} -> {b' : B a'} -> (bq : subst B aq b ≡ b')
      -> C a b -> C a' b'
subst2 refl refl x = x

congd : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
      -> (f : (a : A) -> (b : B a) -> C a b)
      -> {a a' : A} -> (aq : a ≡ a')
      -> {b : B a} -> {b' : B a'} -> (bq : subst B aq b ≡ b')
      -> subst2 aq bq (f a b) ≡ f a' b'
congd f refl refl = refl

congd' : {A : Set}{B : A -> Set}{C : Set}
      -> (f : (a : A) -> (b : B a) -> C)
      -> {a a' : A} -> (aq : a ≡ a')
      -> {b : B a} -> {b' : B a'} -> (bq : subst B aq b ≡ b')
      -> f a b ≡ f a' b'
congd' f refl refl = refl

UIP : {A : Set}{a a' : A}{p q : a ≡ a'} → p ≡ q
UIP {p = refl} {refl} = refl

data JMEq {A : Set} (a : A) : {B : Set} -> B -> Set where
  refl : JMEq a a


≡-jmeq : {A : Set}{a b : A} -> a ≡ b -> JMEq a b
≡-jmeq refl = refl

jmeq-≡ : {A : Set}{a b : A} -> JMEq a b -> a ≡ b
jmeq-≡ refl = refl

jmeq-cong2 : {A : Set}{B : A -> Set}{C : (a : A) -> B a -> Set}
           -> (f : (a : A) -> (b : B a) -> C a b)
           -> {a a' : A} -> JMEq a a'
           -> {b : B a}{b' : B a'} -> JMEq b b'
           -> JMEq (f a b) (f a' b')
jmeq-cong2 f refl refl  = refl

jmeq-subst : {A : Set}{B : A -> Set}
           -> {a a' : A} -> (p : a ≡ a')
           -> {b : B a}
           -> JMEq (subst B p b) b
jmeq-subst refl = refl

jmeq-sym : {A B : Set}{a : A}{b : B} -> JMEq a b -> JMEq b a
jmeq-sym refl = refl

jmeq-trans : {A B C : Set}{a : A}{b : B}{c : C} -> JMEq a b -> JMEq b c -> JMEq a c
jmeq-trans refl refl = refl

postulate
  funext : {A : Set}{B : A -> Set}
           {f g : (a : A) -> B a}
           -> ((a : A) -> f a ≡ g a)
           -> f ≡ g
  ifunext : {A : Set}{B : A -> Set}
            {f g : {a : A} -> B a}
            -> ((a : A) -> f {a} ≡ g {a})
            -> (λ {a} -> f {a}) ≡ g

  jmfunext : {A : Set}{B B' : A -> Set}
            {f : (a : A) -> B a}
            {g : (a : A) -> B' a}
            -> ((a : A) -> JMEq (f a) (g a))
            -> JMEq f g
  jmfunext' : {A A' : Set}{B : Set}
            {f : (a : A) -> B}
            {g : (a' : A') -> B}
            -> ((a : A) -> (a' : A') -> JMEq a a' -> JMEq (f a) (g a'))
            -> JMEq f g
  jmifunext : {A : Set}{B B' : A -> Set}
            {f : {a : A} -> B a}
            {g : {a : A} -> B' a}
            -> ((a : A) -> JMEq (f {a}) (g {a}))
            -> JMEq (λ {a} -> f {a}) (λ {a} -> g {a})



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

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x ,- xs) ++ ys = x ,- xs ++ ys

infixr 5 _++_ _,-_

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

assoc-< : {l n m k : Nat}
        -> (ph : l <= n)(th : n <= m)(ps : m <= k)
        -> ph -< (th -< ps) ≡ (ph -< th) -< ps
assoc-< ph th (skip ps) = cong skip (assoc-< ph th ps)
assoc-< ph (skip th) (suc ps) = cong skip (assoc-< ph th ps)
assoc-< (skip ph) (suc th) (suc ps) = cong skip (assoc-< ph th ps)
assoc-< (suc ph) (suc th) (suc ps) = cong suc (assoc-< ph th ps)
assoc-< ph th zero = refl

unitr-< : {l n : Nat} -> (ph : l <= n) -> (ph -< io) ≡ ph
unitr-< (skip ph) = cong skip (unitr-< ph)
unitr-< (suc ph) = cong suc (unitr-< ph)
unitr-< zero = refl

{-# REWRITE assoc-< #-}
{-# REWRITE unitr-< #-}

no-unique : {k : Nat} → (th : 0 <= k) → th ≡ no
no-unique (skip th) = cong skip (no-unique th)
no-unique zero = refl

no-unique-no : {k : Nat} → no-unique (no {k}) ≡ refl
no-unique-no {zero} = refl
no-unique-no {suc k} rewrite no-unique-no {k} = refl

{-# REWRITE no-unique-no #-}

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
