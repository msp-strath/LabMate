{-# OPTIONS --rewriting #-}
module Model where

open import Lib

Atom : Set
Atom = String

mutual

 data Normal (sc : Nat) : Set where
  ne : Neutral sc -> Normal sc
  atom : Atom -> Normal sc
  pair : Normal sc -> Normal sc -> Normal sc
  bind : Normal (suc sc) -> Normal sc

 record Neutral (sc : Nat) : Set where
  inductive
  constructor neutral
  field
   nut : 1 <= sc
   spine : Bwd (Normal sc)

mutual

 _^t_ : {sc sc' : Nat} -> Normal sc -> sc <= sc' -> Normal sc'
 ne n ^t th = ne (n ^n th)
 atom a ^t th = atom a
 pair s t ^t th = pair (s ^t th) (t ^t th)
 bind t ^t th = bind (t ^t suc th)

 _^n_ : {sc sc' : Nat} -> Neutral sc -> sc <= sc' -> Neutral sc'
 (neutral nut spine) ^n th = neutral (nut -< th) (spine ^tz th)

 _^tz_ : {sc sc' : Nat} -> Bwd (Normal sc) -> sc <= sc' -> Bwd (Normal sc')
 [] ^tz th = []
 (tz -, t) ^tz th = (tz ^tz th) -, (t ^t th)

mutual

  ^t-id : {sc : Nat} -> (t : Normal sc) -> t ^t io ≡ t
  ^t-id (ne x) = cong ne (^n-id x)
  ^t-id (atom a) = refl
  ^t-id (pair s t) = cong2 pair (^t-id s) (^t-id t)
  ^t-id (bind t) = cong bind (^t-id t)

  ^n-id : {sc : Nat} -> (n : Neutral sc) -> n ^n io ≡ n
  ^n-id (neutral nut spine) = cong (neutral nut) (^tz-id spine)

  ^tz-id : {sc : Nat} -> (tz : Bwd (Normal sc)) -> tz ^tz io ≡ tz
  ^tz-id [] = refl
  ^tz-id (tz -, t) = cong2 _-,_ (^tz-id tz) (^t-id t)

mutual

  ^t-comp : {sc sc' sc'' : Nat}
          -> (th : sc <= sc')(ph : sc' <= sc'')
          -> (t : Normal sc) -> (t ^t th) ^t ph ≡ t ^t (th -< ph)
  ^t-comp th ph (ne x) = cong ne (^n-comp th ph x)
  ^t-comp th ph (atom a) = refl
  ^t-comp th ph (pair s t) = cong2 pair (^t-comp th ph s) (^t-comp th ph t)
  ^t-comp th ph (bind t) = cong bind (^t-comp (suc th) (suc ph) t)

  ^n-comp : {sc sc' sc'' : Nat}
          -> (th : sc <= sc')(ph : sc' <= sc'')
          -> (n : Neutral sc) -> (n ^n th) ^n ph ≡ n ^n (th -< ph)
  ^n-comp th ph (neutral nut spine)
    = cong (neutral ((nut -< th) -< ph)) (^tz-comp th ph spine)

  ^tz-comp : {sc sc' sc'' : Nat}
          -> (th : sc <= sc')(ph : sc' <= sc'')
          -> (tz : Bwd (Normal sc)) -> (tz ^tz th) ^tz ph ≡ tz ^tz (th -< ph)
  ^tz-comp th ph [] = refl
  ^tz-comp th ph (tz -, t) = cong2 _-,_ (^tz-comp th ph tz) (^t-comp th ph t)


pattern nil = atom ""

data Type (sc : Nat) : Set
El : {sc : Nat} -> Type sc -> Set
_^ty_ : {sc sc' : Nat} -> Type sc -> sc <= sc' -> Type sc'
^ty-comp : {sc sc' sc'' : Nat}
         -> (A : Type sc)
         -> (th : sc  <= sc')
         -> (ph : sc' <= sc'')
         -> (A ^ty th) ^ty ph ≡ A ^ty (th -< ph)

{-# NO_POSITIVITY_CHECK #-}
data Type sc where
  pi sg : (A : Type sc) -> (B : {sc' : Nat} -> (th : sc <= sc') -> El (A ^ty th) -> Type sc') -> Type sc
  list : Type sc -> Type sc
  one : Type sc
  ne : Neutral sc -> Type sc

{-# TERMINATING #-}
El {sc} (pi A B) = {sc' : Nat} -> (th : sc <= sc') -> (a : El (A ^ty th)) -> El (B th a)
El {sc} (sg A B) = Sg (El (A ^ty io)) λ a -> El (B io a)
El {sc} (list A)  = List (Neutral sc + El A)
El one = One
El {sc} (ne x) = Neutral sc

pi A B ^ty th = pi (A ^ty th) (λ ph a -> B (th -< ph) (subst El (^ty-comp A th ph) a))
sg A B ^ty th = sg (A ^ty th) (λ ph a -> B (th -< ph) (subst El (^ty-comp A th ph) a))
list A ^ty th = list (A ^ty th)
one ^ty th = one
ne x ^ty th = ne (x ^n th)

^ty-comp (pi A B) th ph = jmeq-≡ (jmeq-cong2 pi (≡-jmeq (^ty-comp A th ph))
         (jmifunext λ sc -> jmfunext λ ps ->
         jmfunext' (λ a a' p -> jmeq-cong2 B refl (jmeq-trans (jmeq-subst (^ty-comp A th (ph -< ps)) ) (jmeq-trans (jmeq-subst (^ty-comp (A ^ty th) ph ps)) (jmeq-trans p (jmeq-sym (jmeq-subst (^ty-comp A (th -< ph) ps)))))))))

^ty-comp (sg A B) th ph = jmeq-≡ (jmeq-cong2 sg (≡-jmeq (^ty-comp A th ph))
         (jmifunext λ sc -> jmfunext λ ps ->
         jmfunext' (λ a a' p -> jmeq-cong2 B refl (jmeq-trans (jmeq-subst (^ty-comp A th (ph -< ps)) ) (jmeq-trans (jmeq-subst (^ty-comp (A ^ty th) ph ps)) (jmeq-trans p (jmeq-sym (jmeq-subst (^ty-comp A (th -< ph) ps)))))))))

^ty-comp (list A) th ph = cong list (^ty-comp A th ph)
^ty-comp one th ph = refl
^ty-comp (ne x) th ph = cong ne (^n-comp th ph x)


 {- ElSg
   : {sc tgt : Nat}
   -> (A : Type sc)
   -> (B : {sc' : Nat} (th : sc <= sc') → El (A ^ty th) → Type sc')
   -> (th : sc <= tgt)3
   -> Set
 ElSg {sc} A B = {!Sg Nat λ between -> Sg (sc <= between) λ !} -}



 {-
 El : {sc' : Nat} -> CdB Type sc' -> Set
 El {sc'} (t ^ th) = El' t th

 El' : {sc sc' : Nat} -> Type sc -> sc <= sc' -> Set -- do we really need the thinning if we have _^ty_
 El' {sc} {sc'} (pi a b) th = {sc'' : Nat}(ph : sc' <= sc'')(x : El' a (th -< ph)) -> El' (b (th -< ph) x) io
 El' (sg a b) th = ElSg a b th --Sg (El' a th) (λ x -> El' (b th x) io)
 El' {sc} {sc'} (list a) th = List (Neutral sc' + El' a th)
 El' one th = One
 El' {sc} {sc'} (ne n) th = Neutral sc'



 ElSg :
   {sc tgt : Nat}
   (a : Type sc)
   (b : {sc' : Nat} -> (th : sc <= sc') -> El' a th -> Type sc')
   -> sc <= tgt -> Set
 ElSg {sc} {tgt} a b th =
   Sg Nat λ between -> Sg (sc <= between) λ ph -> Sg (El' a ph) λ witness ->
     Sg (between <= tgt) λ ps -> Sg (El' (b ph witness) ps) λ _ -> th ≡ ph -< ps

sg0 : (a : Type 0) -> (b : {sc' : Nat} -> El (a ^ (no {sc'})) -> Type sc') -> Type 0
sg0 a b = sg a λ th x → b (subst (El' a) (no-unique th) x)

mutual
-}


{-
mutual

  thinEl' : {then now later : Nat}
        -> (ty : Type then)
        -> (th : then <= now)
        -> El' ty th
        -> (ph : now <= later)
        -> El' ty (th -< ph)
  thinEl' (pi a b) th f ph = λ ps x → f (ph -< ps) x
  thinEl' (sg a b) th (between , ph , witness , ps , y , refl) ch =
    between , ph , witness , (ps -< ch) , thinEl' (b ph witness) ps y ch , refl
  thinEl' (list ty) th x ph = map (bimap (_^n ph) (λ y → thinEl' ty th y ph)) x
  thinEl' one th x ph = tt
  thinEl' (ne _) th x ph = x ^n ph

mutual

 quoteType : {sc : Nat} -> Type sc -> Normal sc
 quoteType (pi a b) = pair (atom "Pi") (pair (quoteType a) (pair (bind (quoteType (b (skip io) (unquoteEl a (skip io) (neutral (suc no) []))))) nil))
 quoteType (sg a b) = pair (atom "Sg") (pair (quoteType a) (pair (bind (quoteType (b (skip io) (unquoteEl a (skip io) (neutral (suc no) []))))) nil))
 quoteType (list a) = pair (atom "List") (pair (quoteType a) nil)
 quoteType one = pair (atom "One") nil
 quoteType (ne n) = ne n

 unquoteEl : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') -> Neutral sc' -> El' a th
 unquoteEl (pi a b) th (neutral nut spine) = λ ph x -> unquoteEl (b (th -< ph) x) io (neutral (nut -< ph) ((spine ^tz ph) -, quoteEl a (th -< ph) x))
 unquoteEl {sc} {sc'} (sg a b) th (neutral nut spine) = let a' = unquoteEl a th (neutral nut (spine -, atom "fst")) in
   _ , th , a' , io , unquoteEl (b th a') io (neutral nut (spine -, atom "snd")) , refl
 unquoteEl (list a) _ n = inl n ,- []
 unquoteEl one _ n = tt
 unquoteEl (ne N) _ n = n

 quoteEl : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') ->  El' a th -> Normal sc'
 quoteEl (pi a b) th f = let x = (unquoteEl a (skip th) (neutral (suc no) [])) in
  bind (quoteEl (b (skip th) x) (suc io) (f (skip io) x ))
 quoteEl (sg a b) th (between , ph , witness , ps , y , q)  = pair (quoteEl a ph witness ^t ps) (quoteEl (b ph witness) ps y)
 quoteEl (list a) th xs = quoteList a th xs
 quoteEl one _ _ = nil
 quoteEl (ne N) _ n = ne n

 quoteList : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') -> List (Neutral sc' + El' a th) -> Normal sc'
 quoteList a th [] = nil
 quoteList a th (inl n ,- xs) = pair (atom "plus") (pair (ne n) (quoteList a th xs))
 quoteList a th (inr t ,- xs) = pair (atom "plus") (pair (pair (atom "one") (quoteEl a th t)) (quoteList a th xs))


mutual

  data Context : (k : Nat) → Set where
    ε : Context 0
    _,_ : {k : Nat} → (Γ : Context k) → (∀ {m} → El' ∣ Γ ∣ (no {m}) → Type m) → Context (suc k)

  ∣_∣ : ∀ {k} → Context k → Type 0
  ∣ ε ∣ = one
  ∣ Γ , B ∣ = sg0 ∣ Γ ∣ B

Env : ∀ {k'} → (k : Nat) → Context k' → Set
Env k Γ = El' ∣ Γ ∣ (no {k})

closeType : {sc m : Nat} -> Type sc -> (Ga : Context sc) -> El' ∣ Ga ∣ (no {m}) -> Type m
closeType A ε x = {!!}
closeType A (Ga , x₁) x = {!!}
-- lookup : {sc : Nat} -> 1 <= sc -> Context sc -> (∀ {m} → El' ∣ Γ ∣ (no {m}) → Type m)

{-
  data Context (n : Nat) : (k : Nat) → Set where
    ε : Context n 0
    _,_ : {k : Nat} → (Γ : Context n k) → (∀ {m} → (th : n <= m) → El' ∣ Γ ∣ th → Type m) → Context n (suc k)

  ∣_∣ : ∀ {n k} → Context n k → Type n
  ∣ ε ∣ = one
  ∣ Γ , B ∣ = sg ∣ Γ ∣ (λ th γ → B th γ)

Env : ∀ {k'} → (k : Nat) → Context 0 k' → Set
Env k Γ = El' ∣ Γ ∣ (no {k})
-}
-}
