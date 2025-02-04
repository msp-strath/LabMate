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

pattern nil = atom ""

mutual

 data Type (sc : Nat) : Set where
  pi sg : (a : Type sc) -> (b : {sc' : Nat} -> (th : sc <= sc') -> El (a ^ th) -> Type sc') -> Type sc
  list : Type sc -> Type sc
  one : Type sc
  ne : Neutral sc -> Type sc


 El : {sc' : Nat} -> CdB Type sc' -> Set
 El {sc'} (t ^ th) = El' t th

 El' : {sc sc' : Nat} -> Type sc -> sc <= sc' -> Set
 El' {sc} {sc'} (pi a b) th = {sc'' : Nat}(ph : sc' <= sc'')(x : El' a (th -< ph)) -> El' (b (th -< ph) x) io
 El' (sg a b) th = ElSg a b th --Sg (El' a th) (λ x -> El' (b th x) io)
 El' {sc} {sc'} (list a) th = List (Neutral sc' + El' a th)
 El' one th = One
 El' {sc} {sc'} (ne n) th = Neutral sc'

{-
 El : {src : Nat} -> Type src -> (tgt : Nat) -> Set
 El (pi a b) tgt = {tgt' : Nat}(th : tgt <= tgt')(x : El a tgt') -> El (b x) tgt'
 El (sg a b) tgt = ElSg a b tgt
 El (list a) tgt = List (Neutral tgt + El a tgt)
 El one _ = One
 El (ne n) tgt = Neutral tgt
-}

 ElSg :
   {sc tgt : Nat}
   (a : Type sc)
   (b : {sc' : Nat} -> (th : sc <= sc') -> El' a th -> Type sc')
   -> sc <= tgt -> Set
 ElSg {sc} {tgt} a b th =
   Sg Nat λ between -> Sg (sc <= between) λ ph -> Sg (El' a ph) λ witness ->
     Sg (between <= tgt) λ ps -> Sg (El' (b ph witness) ps) λ _ -> th ≡ ph -< ps

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
