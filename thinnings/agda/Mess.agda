module Mess where

kk : forall {i j}{A : Set i}{B : Set j} -> A -> B -> A
kk a _ = a

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A)(b : B a) -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A) -> C a (f a)
(f - g) a = g (f a)

record One : Set where constructor <>

data _~_ {X : Set}(x : X) : X -> Set where
  r~ : x ~ x
infix 20 _~_

module _ {X : Set}(x : X) where

  _~[_>_ : {y z : X} -> x ~ y -> y ~ z -> x ~ z
  _~[_>_ r~ q = q

  _<_]~_ : {y z : X} -> y ~ x -> y ~ z -> x ~ z
  _<_]~_ r~ q = q

  R~ _[QED] : x ~ x
  _[QED] = r~
  R~ = r~

  infixr 2 _~[_>_ _<_]~_
  infixr 3 _[QED]

_~$~_ : {S T : Set}
  {f g : S -> T} -> f ~ g ->
  {x y : S} -> x ~ y ->
  f x ~ g y
r~ ~$~ r~ = r~

infixl 4 _~$~_

data List (X : Set) : Set where
  [] : List X
  _,-_ : X -> List X -> List X

infixr 30 _,-_

module _ {X : Set} where

  infixr 30 _++_

  [_] : X -> List X
  [ x ] = x ,- []

  _++_ : List X -> List X -> List X
  [] ++ ys = ys
  (x ,- xs) ++ ys = x ,- xs ++ ys

  _++[] : (xs : List X) -> xs ++ [] ~ xs
  [] ++[] = r~
  (x ,- xs) ++[] = R~ (x ,-_) ~$~ (xs ++[])

  assoc++ : (xs ys zs : List X) -> (xs ++ ys) ++ zs ~ xs ++ ys ++ zs
  assoc++ [] ys zs = r~
  assoc++ (x ,- xs) ys zs = R~ (x ,-_) ~$~ assoc++ xs ys zs

  infix 20 _<=_
  data _<=_ : List X -> List X -> Set where
    _^-_ : (x : X){xs ys : List X} -> xs <= ys ->      xs <= x ,- ys
    _,-_ : (x : X){xs ys : List X} -> xs <= ys -> x ,- xs <= x ,- ys
    [] : [] <= []

  no : forall {xs} -> [] <= xs
  no {[]} = []
  no {x ,- xs} = x ^- no

  noes : forall {xs}{th ph : [] <= xs} -> th ~ ph
  noes {th = x ^- th} {.x ^- ph} = R~ (x ^-_) ~$~ noes
  noes {th = []} {[]} = r~

  io : forall {xs} -> xs <= xs
  io {[]} = []
  io {x ,- xs} = x ,- io

  module _ (P : X -> Set) where
  
    data All : List X -> Set where
      [] : All []
      _,-_ : forall {x xs} -> P x -> All xs -> All (x ,- xs)

  module _ {P : X -> Set} where
  
    _<?_ : forall {xs ys} -> xs <= ys -> All P ys -> All P xs
    (x ^- th) <? (p ,- ps) = th <? ps
    (x ,- th) <? (p ,- ps) = p ,- (th <? ps)
    [] <? [] = []

    only : forall {x} -> All P (x ,- []) -> P x
    only (p ,- _) = p

    _!!_ : forall {xs x} -> All P xs -> x ,- [] <= xs -> P x
    ps !! i = only (i <? ps)

    tab : forall {xs} -> (forall {x} -> x ,- [] <= xs -> P x) -> All P xs
    tab {[]} f = []
    tab {x ,- xs} f = f (x ,- no) ,- tab ((x ^-_) - f)

    tab!! : forall {xs}(f : forall {x} -> x ,- [] <= xs -> P x)
      {x}(i : x ,- [] <= xs) -> (tab f !! i) ~ f i
    tab!! f (x ^- i) = tab!! ((x ^-_) - f) i
    tab!! f (x ,- i) = R~ ((x ,-_) - f) ~$~ noes

module _ {S T : Set}(f : S -> List T) where

  klex : List S -> List T
  klex [] = []
  klex (s ,- ss) = f s ++ klex ss

  klex-cat : (ss0 ss1 : List S) -> klex (ss0 ++ ss1) ~ klex ss0 ++ klex ss1
  klex-cat [] ss1 = r~
  klex-cat (s ,- ss0) ss1 = 
    f s ++ klex (ss0 ++ ss1) ~[ R~ (f s ++_) ~$~ klex-cat ss0 ss1 >
    f s ++ (klex ss0 ++ klex ss1) < assoc++ (f s) (klex ss0) (klex ss1) ]~
    (f s ++ klex ss0) ++ klex ss1 [QED]

module _ {S T : Set}(f : S -> T) where

  list : List S -> List T
  list = klex (f - [_])
  
Nat = List One
pattern ze = []
pattern su n = <> ,- n
one : Nat
one = su ze

data `List ( l  -- how many list *elements*
             v  -- how many list *variables*
           : Nat) : Set where
  `[]   : `List l v
  `[_]  : one <= l -> `List l v
  _`++_ : `List l v -> `List l v -> `List l v
  `#    : one <= v -> `List l v


data Chunk (l v : Nat) : Set where
  `[_] : one <= l -> Chunk l v
  `#   : one <= v -> Chunk l v

listNorm : {l v : Nat} -> `List l v -> List (Chunk l v)
listNorm `[] = []
listNorm `[ e ] = `[ e ] ,- []
listNorm (s `++ t) = listNorm s ++ listNorm t
listNorm (`# xs) = `# xs ,- []

module _ {X : Set}{l v : Nat} where

  module _ (rh : All (kk X) l)(sg : All (kk (List X)) v)  where

    listEval : `List l v -> List X
    listEval `[] = []
    listEval `[ e ] = (rh !! e) ,- []
    listEval (s `++ t) = listEval s ++ listEval t
    listEval (`# xs) = sg !! xs

    chunkEval : Chunk l v -> List X
    chunkEval `[ e ] = (rh !! e) ,- []
    chunkEval (`# xs) = sg !! xs

    evalViaNorm : (t : `List l v) -> listEval t ~ klex chunkEval (listNorm t)
    evalViaNorm `[] = r~
    evalViaNorm `[ e ] = r~
    evalViaNorm (s `++ t) = 
      listEval s ++ listEval t ~[ R~ _++_ ~$~ evalViaNorm s ~$~ evalViaNorm t >
      klex chunkEval (listNorm s) ++ klex chunkEval (listNorm t)
        < klex-cat chunkEval (listNorm s) (listNorm t) ]~
      klex chunkEval (listNorm s ++ listNorm t) [QED]
    evalViaNorm (`# xs) = 
      (sg !! xs) < (sg !! xs) ++[] ]~
      (sg !! xs) ++ ze [QED]

    normSound : (s t : `List l v) -> listNorm s ~ listNorm t
             -> listEval s ~ listEval t
    normSound s t q = 
      listEval s ~[ evalViaNorm s >
      klex chunkEval (listNorm s) ~[ R~ (klex chunkEval) ~$~ q >
      klex chunkEval (listNorm t) < evalViaNorm t ]~
      listEval t [QED]

module _ {l v : Nat} where

  normViaEval : (t : `List l v) -> listNorm t ~ listEval (tab `[_]) (tab (`# - [_])) t
  normViaEval `[] = r~
  normViaEval `[ e ] = 
    `[ e ] ,- ze <  R~ (_,- []) ~$~ tab!! `[_] e ]~
    (tab `[_] !! e) ,- ze [QED]
  normViaEval (s `++ t) = R~ _++_ ~$~ normViaEval s ~$~ normViaEval t
  normViaEval (`# xs) =
    `# xs ,- ze < tab!! (`# - [_]) xs ]~
    (tab (`# - [_]) !! xs) [QED]

  normComplete : (s t : `List l v)
    -> ({X : Set}(rh : All (kk X) l)(sg : All (kk (List X)) v) -> listEval rh sg s ~ listEval rh sg t)
    -> listNorm s ~ listNorm t
  normComplete s t qs = 
    listNorm s ~[ normViaEval s >
    listEval (tab `[_]) (tab (`# - [_])) s ~[ qs _ _ >
    listEval (tab `[_]) (tab (`# - [_])) t < normViaEval t ]~
    listNorm t [QED]
