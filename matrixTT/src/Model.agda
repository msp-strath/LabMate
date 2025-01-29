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
  pi sg : (a : Type sc) -> (b : {sc' : Nat} -> {-  sc <= sc' -> -} El a sc' -> Type sc') -> Type sc
  list : Type sc -> Type sc
  one : Type sc
  ne : Neutral sc -> Type sc

{-
 El : {sc' : Nat} -> CdB Type sc' -> Set
 El {sc'} (t ^ th) = El' th t

 El' : {sc sc' : Nat} -> sc <= sc' -> Type sc -> Set
 El' {sc} {sc'} th (pi a b) = {sc'' : Nat}(ph : sc' <= sc'')(x : El' (th -< ph) a) -> El' io (b (th -< ph) x )
 El' th (sg a b) = Sg (El' th a) (λ x -> El' io (b th x))
 El' {sc} {sc'} th (list a) = List (Neutral sc' + El' th a)
 El' th one = One
 El' {sc} {sc'} th (ne n) = Neutral sc'
-}

 El : {src : Nat} -> Type src -> (tgt : Nat) -> Set
 El (pi a b) tgt = {tgt' : Nat}(th : tgt <= tgt')(x : El a tgt') -> El (b x) tgt'
 El (sg a b) tgt = ElSg a b tgt
 El (list a) tgt = List (Neutral tgt + El a tgt)
 El one _ = One
 El (ne n) tgt = Neutral tgt

 ElSg :
   {sc : Nat}
   (a : Type sc)
   (b : {sc' : Nat} -> El a sc' -> Type sc')
   (tgt : Nat) -> Set
 ElSg a b tgt = Sg Nat λ yesterday -> Sg (El a yesterday) λ witness -> Sg (yesterday <= tgt) λ history -> El (b witness) tgt

mutual

  _^el_ : {src tgt tgt' : Nat} -> {ty : Type src}
        -> El ty tgt -> tgt <= tgt' -> El ty tgt'
  _^el_ {ty = pi ty b} f th = λ ph x -> f (th -< ph) x
  _^el_ {ty = sg ty b} (_ , x , ph , y) th = _ , x , (ph -< th) , (y ^el th)
  _^el_ {ty = list ty} x th = map (bimap (_^n th) (_^el th)) x
  _^el_ {ty = one} x th = tt
  _^el_ {ty = ne _} x th = x ^n th


mutual

 quoteType : {sc : Nat} -> Type sc -> Normal sc
 quoteType (pi a b) = pair (atom "Pi") (pair (quoteType a) (pair (bind (quoteType (b (unquoteEl a (neutral (suc no) []))))) nil))
 quoteType (sg a b) = pair (atom "Sg") (pair (quoteType a) (pair (bind (quoteType (b (unquoteEl a (neutral (suc no) []))))) nil))
 quoteType (list a) = pair (atom "List") (pair (quoteType a) nil)
 quoteType one = pair (atom "One") nil
 quoteType (ne n) = ne n

 unquoteEl : {sc sc' : Nat} -> (a : Type sc) -> Neutral sc' -> El a sc'
 unquoteEl (pi a b) (neutral nut spine) = λ ph x -> unquoteEl (b x) (neutral (nut -< ph) ((spine ^tz ph) -, quoteEl a x))
 unquoteEl {sc} {sc'} (sg a b) (neutral nut spine) = let a' = unquoteEl a (neutral nut (spine -, atom "fst")) in
   _ , a' , io , unquoteEl (b a') (neutral nut (spine -, atom "snd"))
 unquoteEl (list a) n = inl n ,- []
 unquoteEl one n = tt
 unquoteEl (ne N) n = n

 quoteEl : {sc sc' : Nat} -> (a : Type sc) -> El a sc' -> Normal sc'
 quoteEl (pi a b) f = let x = (unquoteEl a (neutral (suc no) [])) in
  bind (quoteEl (b x) (f (skip io) x))
 quoteEl (sg a b) (_ , s , ph , t) = pair (quoteEl a s ^t ph) (quoteEl (b s) t)
 quoteEl (list a) xs = quoteList a xs
 quoteEl one _ = nil
 quoteEl (ne N) n = ne n

 quoteList : {sc sc' : Nat} -> (a : Type sc) -> List (Neutral sc' + El a sc') -> Normal sc'
 quoteList a [] = nil
 quoteList a (inl n ,- xs) = pair (atom "plus") (pair (ne n) (quoteList a xs))
 quoteList a (inr t ,- xs) = pair (atom "plus") (pair (pair (atom "one") (quoteEl a t)) (quoteList a xs))
