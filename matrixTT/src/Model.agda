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
 El {sc'} (t ^ th) = El' th t

 El' : {sc sc' : Nat} -> sc <= sc' -> Type sc -> Set
 El' {sc} {sc'} th (pi a b) = {sc'' : Nat}(ph : sc' <= sc'')(x : El' (th -< ph) a) -> El' io (b (th -< ph) x )
 El' th (sg a b) = Sg (El' th a) (λ x -> El' io (b th x))
 El' {sc} {sc'} th (list a) = List (Neutral sc' + El' th a)
 El' th one = One
 El' {sc} {sc'} th (ne n) = Neutral sc'


mutual

 quoteType : {sc : Nat} -> Type sc -> Normal sc
 quoteType (pi a b) = pair (atom "Pi") (pair (quoteType a) (pair (bind (quoteType (b (skip io) (unquoteEl a (skip io) (neutral (suc no) []))))) nil))
 quoteType (sg a b) = pair (atom "Sg") (pair (quoteType a) (pair (bind (quoteType (b (skip io) (unquoteEl a (skip io) (neutral (suc no) []))))) nil))
 quoteType (list a) = pair (atom "List") (pair (quoteType a) nil)
 quoteType one = pair (atom "One") nil
 quoteType (ne n) = ne n

 unquoteEl : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') -> Neutral sc' -> El (a ^ th)
 unquoteEl (pi a b) th (neutral nut spine) = λ ph x -> unquoteEl (b (th -< ph) x) io (neutral (nut -< ph) ((spine ^tz ph) -, quoteEl a (th -< ph) x))
 unquoteEl {sc} {sc'} (sg a b) th (neutral nut spine) = let a' = unquoteEl a th (neutral nut (spine -, atom "fst")) in
  (a' , unquoteEl (b th a') io (neutral nut (spine -, atom "snd")))
 unquoteEl (list a) th n = inl n ,- []
 unquoteEl one th n = tt
 unquoteEl (ne N) th n = n

 quoteEl : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') -> El (a ^ th) -> Normal sc'
 quoteEl (pi a b) th f = let x = (unquoteEl a (th -< skip io) (neutral (suc no) [])) in
  bind (quoteEl (b (th -< skip io) x) io (f (skip io) x))
 quoteEl (sg a b) th (s , t) = pair (quoteEl a th s) (quoteEl (b th s) io t)
 quoteEl (list a) th xs = quoteList a th xs
 quoteEl one th _ = nil
 quoteEl (ne N) th n = ne n

 quoteList : {sc sc' : Nat} -> (a : Type sc) -> (th : sc <= sc') -> List (Neutral sc' + El (a ^ th)) -> Normal sc'
 quoteList a th [] = nil
 quoteList a th (inl n ,- xs) = pair (atom "plus") (pair (ne n) (quoteList a th xs))
 quoteList a th (inr t ,- xs) = pair (atom "plus") (pair (pair (atom "one") (quoteEl a th t)) (quoteList a th xs))
