module Lump where

------------------------------------------------
data Zero' : Set where
record Zero : Set where field {.bad} : Zero'
record One : Set where constructor <>
data Two : Set where ff tt : Two

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_
infixr 10 _,_ _*_
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

module _ {X : Set} where

  <:_:> [:_:] : (X -> Set) -> Set
  <: P :> = X >< P
  [: P :] = (x : X) -> P x
  infix 5 <:_:> [:_:]

  _*:_ _-:>_ : (P Q : X -> Set) -> (X -> Set)
  (P *: Q) x = P x * Q x
  (P -:> Q) x = P x -> Q x
  infixr 10 _*:_
  infixr 7 _-:>_

  data _~_ (x : X) : X -> Set where
    r~ : x ~ x

module _ {X : Set}(R : X -> X -> Set) where

  data Star (x : X) : X -> Set where
    [] : Star x x
    _,-_ : {y z : X} -> R x y -> Star y z -> Star x z

  _+*+_ : forall {x y z} -> Star x y -> Star y z -> Star x z
  [] +*+ ys = ys
  (x ,- xs) +*+ ys = x ,- (xs +*+ ys)

------------------------------------------------


data List (X : Set) : Set where
  []   : List X
  _,-_ : X -> List X -> List X

infixr 20 _,-_

module _ {X : Set} where

  infix 15 [_++_]~_
  data [_++_]~_ : List X -> List X -> List X -> Set where
    [] : forall {ys} -> [ [] ++ ys ]~ ys
    _,-_ : forall x {xs ys zs}
        -> [ xs ++ ys ]~ zs -> [ x ,- xs ++ ys ]~ x ,- zs

  cat : forall xs ys -> <: [ xs ++ ys ]~_ :>
  cat [] _ = _ , []
  cat (_ ,- _) _ = let _ , zs = cat _ _ in _ , _ ,- zs

  catQ : forall {xs ys}(a b : <: [ xs ++ ys ]~_ :>) -> a ~ b
  catQ (_ , []) (_ , []) = r~
  catQ (_ , (x ,- a)) (_ , (.x ,- b))
    with r~ <- catQ (_ , a) (_ , b) = r~

  infix 15 _=J-_
  data _=J-_ : List (List X) -> List X -> Set where
    [] : [] =J- []
    _,+_ : forall {xs xss ys zs}
        -> [ xs ++ ys ]~ zs -> xss =J- ys
        -> xs ,- xss =J- zs

  cats : forall xss -> <: xss =J-_ :>
  cats [] = _ , []
  cats (_ ,- _) = 
    let _ , x = cat _ _ in
    let _ , xj = cats _ in
    _ , x ,+ xj

  catsQ : forall {xss}(a b : <: xss =J-_ :>) -> a ~ b
  catsQ (_ , []) (_ , []) = r~
  catsQ (_ , (x ,+ a)) (_ , (y ,+ b))
    with r~ <- catsQ (_ , a) (_ , b)
    with r~ <- catQ (_ , x) (_ , y)
       = r~

  asso03 : forall {s01 s02 s13 s23}
        -> <: [ s01 ++_]~ s02 *: [_++ s23 ]~ s13 :>
        -> <: [ s01 ++ s13 ]~_ *: [ s02 ++ s23 ]~_ :>
  asso03 (_ , [] , v123) = _ , [] , v123
  asso03 (_ , (x ,- v012) , v123) = 
    let _ , v013 , v023 = asso03 (_ , v012 , v123) in
    _ , x ,- v013 , x ,- v023

  asso02 : forall {s01 s03 s12 s23}
        -> <: [ s01 ++_]~ s03 *: [ s12 ++ s23 ]~_ :>
        -> <: [ s01 ++ s12 ]~_ *: [_++ s23 ]~ s03 :>
  asso02 {s01} (_ , v013 , v123)
    with _ , v012 <- cat s01 _
    with _ , v013' , v023 <- asso03 (_ , v012 , v123)
    with r~ <- catQ (_ , v013) (_ , v013')
       = _ , v012 , v023


  catNel : forall {xs y ys zs} -> [ xs ++ y ,- ys ]~ zs
    -> X >< \ z -> List X >< \ ws -> zs ~ (z ,- ws)
  catNel [] = _ , _ , r~
  catNel (x ,- v) = _ , _ , r~


  allRight : forall {xs ys} -> [ xs ++ ys ]~ ys -> xs ~ []
  noSmaller : forall {xs y ys}
           -> [ xs ++ y ,- ys ]~ ys
           -> Zero
  allRight [] = r~
  allRight {x ,- xs}{.x ,- ys} (x ,- xyy)
    with () <- noSmaller xyy
  noSmaller v
    with _ , va , vb <- asso02 (_ , v , (_ ,- []))
    with r~ <- allRight vb
    with _ , _ , () <- catNel va



module _ {X : Set} where

  catses : forall {xss}{xs : List X}{yss ys zss}
        -> [ xss ++ yss ]~ zss
        -> xss =J- xs
        -> yss =J- ys
        -> <: zss =J-_ *: [ xs ++ ys ]~_ :>
  catses [] [] ys = _ , ys , []
  catses (_ ,- xyz) (x ,+ xs) ys
    with _ , xz , v <- catses xyz xs ys
    with _ , u , w <- asso03 (_ , x , v)
       = _ , u ,+ xz , w

        
module LUMP (X : Set) where

  Lilist = List (List X)
  _=L=_ : Lilist -> Lilist -> Set
  xss =L= zss = <: xss =J-_ *: zss =J-_ :>

  idL : forall {xss} -> xss =L= xss
  idL {[]} = _ , [] , []
  idL {_ ,- _} = 
    let _ , ls , rs = idL in
    let _ , l = cat _ _ in
    let _ , r = cat _ _ in
    _ , l ,+ ls , r ,+ rs

  coL : forall {xss yss zss}
     -> xss =L= yss
     -> yss =L= zss
     -> xss =L= zss
  coL (_ , x , yl) (_ , yr , z)
    with r~ <- catsQ (_ , yl) (_ , yr)
       = _ , x , z

  oneL : [] =L= []
  oneL = idL

  tenL : forall {ass bss css dss ess fss}
      -> [ ass ++ bss ]~ css
      -> ass =L= dss
      -> bss =L= ess
      -> [ dss ++ ess ]~ fss
      -> css =L= fss
  tenL abc (_ , a , d) (_ , b , e) def
    with _ , c , v <- catses abc a b
       | _ , f , w <- catses def d e
    with r~ <- catQ (_ , v) (_ , w)
    = _ , c , f

  -- Two is "are we in an inner list?"
  data Step : (Two * List X) -> (Two * List X) -> Set where
    `[ : {xs : List X} -> Step (ff , xs) (tt , xs)
    ` : (x : X){xs : List X} -> Step (tt , x ,- xs) (tt , xs)
    `] : {xs : List X} -> Step (tt , xs) (ff , xs)

  Chopped : Two * List X -> Set
  Chopped (ff , zs) = <: _=J- zs :>
  Chopped (tt , zs) =
    List X >< \ xs -> Lilist >< \ yss ->
    <: [ xs ++_]~ zs *: yss =J-_ :>

  stepsEmbiggen : forall {a b zs ys}
    -> Star Step (a , zs) (b , ys) -> <: [_++ ys ]~ zs :>
  stepsEmbiggen [] = _ , []
  stepsEmbiggen (`[ ,- ss) = stepsEmbiggen ss
  stepsEmbiggen (` x ,- ss)
    with _ , v <- stepsEmbiggen ss
       = _ , x ,- v
  stepsEmbiggen (`] ,- ss) = stepsEmbiggen ss

  chop : forall {b xs ys zs} -> [ xs ++ ys ]~ zs
      -> Star Step (b , zs) (ff , ys) -> Chopped (b , xs)
  chop xyz [] with r~ <- allRight xyz = _ , []
  chop xyz (`[ ,- ss)
    with _ , _ , _ , xyz , yj <- chop xyz ss = _ , xyz ,+ yj
  chop [] (` x ,- ss)
    with _ , v <- stepsEmbiggen ss
    with () <- noSmaller v
  chop (.x ,- xyz) (` x ,- ss)
    with _ , _ , _ , xyz , yj <- chop xyz ss
       = _ , _ , _ , x ,- xyz , yj
  chop xyz (`] ,- ss)
    with _ , yj <- chop xyz ss
       = _ , _ , _ , [] , yj


  chop' : forall {bxs} -> Star Step bxs (ff , []) -> Chopped bxs
  chop' [] = _ , []
  chop' (`[ ,- ss) = let _ , _ , _ , xyz , yj = chop' ss in
    _ , (xyz ,+ yj)
  chop' (` x ,- ss) = let _ , _ , _ , xyz , yj = chop' ss in
    _ , _ , _ , (x ,- xyz) , yj
  chop' (`] ,- ss) = let _ , yj = chop' ss in
    _ , _ , _ , [] , yj

  stepff : forall {zs yss}
        -> yss =J- zs -> Star Step (ff , zs) (ff , [])
  steptt : forall {zs} -> Chopped (tt , zs) ->  Star Step (tt , zs) (ff , [])
  stepff [] = []
  stepff (x ,+ yj) =
    `[ ,- steptt (_ , _ , _ , x , yj)
  steptt (_ , _ , _ , [] , yj) =
    `] ,- stepff yj
  steptt (_ , _ , _ , (x ,- x') , yj) =
    ` x ,- steptt (_ , _ , _ , x' , yj)

{-
  chop : forall {b} -> Star Step b ff -> Chopped b
  chop [] = []
  chop (`[ ,- xs) = let ys , yss = chop xs in ys ,- yss 
  chop (` x ,- xs) = let ys , yss = chop xs in (x ,- ys) , yss
  chop (`] ,- xs) = [] , chop xs

  elts : forall {a b} -> Star Step a b -> List X
  elts [] = []
  elts (`[ ,- xs) = elts xs
  elts (` x ,- xs) = x ,- elts xs
  elts (`] ,- xs) = elts xs
-}


{-

  data Cut : List X -> Set where
    [] : Cut []
    _,-_ : forall x {xs} -> Cut xs -> Cut (x ,- xs)
    !_ : forall {xs} -> Cut xs -> Cut xs

  cut : forall {zs} -> Cut zs ->
    List X >< \ xs ->
    List X >< \ ys ->
    [ xs ++ ys ]~ zs * <: _=J- ys :>
  cut [] = _ , _ , [] , _ , []
  cut (x ,- xc) =
    let _ , _ , xyz , _ , yj = cut xc in
    _ , _ , x ,- xyz , _ , yj
  cut (! xc) =
    let _ , _ , xyz , _ , yj = cut xc in
    _ , _ , [] , _ , (xyz ,+ yj)

  tuc : forall {xs yss ys zs}
     -> (xyz : [ xs ++ ys ]~ zs)
     -> (yj : yss =J- ys)
     -> Cut zs >< \ zc
     -> cut zc ~ (_ , _ , xyz , _ , yj)
  tuc [] [] = [] , r~
  tuc [] (x ,+ yj)
    with zc , r~ <- tuc x yj
       = ! zc , r~
  tuc (x ,- xyz) yj
    with zc , r~ <- tuc xyz yj
       = x ,- zc , r~ 

  CutApart : forall {xs} -> Cut xs -> Cut xs -> Set
  CutApart [] c2 = One
  CutApart (x ,- c1) (.x ,- c2) = CutApart c1 c2
  CutApart (x ,- c1) (! c2) = CutApart (x ,- c1) c2
  CutApart (! c1) [] = One
  CutApart (! c1) (x ,- c2) = CutApart c1 (x ,- c2)
  CutApart (! c1) (! c2) = Zero

data Nat : Set where
  ze : Nat
  su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module TEST where
  open LUMP Nat


-}
