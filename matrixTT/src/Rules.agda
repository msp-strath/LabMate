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

Context : Nat -> Set
Context sc = Stack (CdB Type sc) sc

ext : {sc : Nat} -> Context sc -> CdB Type sc -> Context (suc sc)
ext xz t = stack (λ (t ^ th) -> t ^ skip th) (xz -, t)

Env : {sc sc' : Nat} -> Stack (CdB Type sc') sc -> (tgt : Nat) -> Set
Env [] _ = One
Env (xz -, (x ^ _)) tgt = Sg (Env xz tgt) (λ _ -> El x tgt)

mutual
 -- magic version

 data _|-TYPE_ {sc : Nat} (Ga : Context sc) : Term sc -> Set where
   one : Ga |-TYPE (pair (atom "One") nil)
   list : {a : Term sc} -> Ga |-TYPE a -> Ga |-TYPE pair (atom "List") (pair a nil)
   pi : {a : Term sc} {b : Term (suc sc)}
      -> (aOk : Ga |-TYPE a)
      -> ext Ga ( [ aOk ]TYPE {!!} ^ io) |-TYPE b
      -> Ga |-TYPE (pair (atom "Pi") (pair a (pair (bind b) nil)))


 [_]TYPE : {sc sc' : Nat} {Ga : Context sc} {ty : Term sc}
         ->  Ga |-TYPE ty -> Env Ga sc' -> Type sc'
 [ one ]TYPE _ = one
 [ list a ]TYPE rho = list ([ a ]TYPE rho)
 [ pi a b ]TYPE rho = pi ([ a ]TYPE rho) (λ x -> [ b ]TYPE {!rho!})
