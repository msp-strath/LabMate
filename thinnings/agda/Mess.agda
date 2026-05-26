module Mess where

kk : forall {i j}{A : Set i}{B : Set j} -> A -> B -> A
kk a _ = a

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A)(b : B a) -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A) -> C a (f a)
(f - g) a = g (f a)

record One : Set where constructor <>

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T
infixr 10 _,_ _*_

module _ {S : Set}(T : S -> Set) where

  <:_:> [:_:] : Set
  <:_:> = S >< T
  [:_:] = (s : S) -> T s

  infix 5 <:_:> [:_:]

  _*:_ : (S -> Set) -> (S -> Set)
  _*:_ U s = T s * U s

  infixr 10 _*:_

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

module _ {X Y : Set}(R : X -> Y -> Set) where

  data ListR : List X -> List Y -> Set where
    [] : ListR [] []
    _,-_ : forall {x xs y ys} -> R x y -> ListR xs ys -> ListR (x ,- xs) (y ,- ys)

module _ {X : Set} where

  infixr 30 _++_

  [_] : X -> List X
  [ x ] = x ,- []

  data [_++_]~_ : List X -> List X -> List X -> Set where
   [] : forall {ys} -> [ [] ++ ys ]~ ys
   _,-_ : forall {xs ys zs} x
       -> [ xs ++ ys ]~ zs -> [ x ,- xs ++ ys ]~ x ,- zs

  infix 20 [_++_]~_

  append : (xs ys : List X) -> <: [ xs ++ ys ]~_ :>
  append [] ys = _ , []
  append (x ,- xs) ys = let _ , zs = append xs ys in _ , x ,- zs

  append! : {xs ys : List X}(p q : <: [ xs ++ ys ]~_ :>) -> p ~ q
  append! (_ , []) (_ , []) = r~
  append! (_ , (x ,- p)) (_ , (.x ,- q))
    with r~ <- append! (_ , p) (_ , q) = r~

  _++_ : List X -> List X -> List X
  xs ++ ys = fst (append xs ys)

  asso++13 : forall {xs01 xs12 xs02 xs23 xs03}
        -> [ xs01 ++ xs12 ]~ xs02
        -> [ xs02 ++ xs23 ]~ xs03
        -> <: [ xs01 ++_]~ xs03 *: [ xs12 ++ xs23 ]~_ :>
  asso++13 [] q = _ , [] , q
  asso++13 (x ,- p) (.x ,- q)
    with _ , r , s <- asso++13 p q = _ , x ,- r , s
        
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

  _-<_ : forall {xs ys zs} -> xs <= ys -> ys <= zs -> xs <= zs
  th -< (x ^- ph) = x ^- (th -< ph)
  (.x ^- th) -< (x ,- ph) = x ^- (th -< ph)
  (.x ,- th) -< (x ,- ph) = x ,- (th -< ph)
  [] -< [] = []

  _+[_<_]+_ : forall {xs0 ys0 xs1 ys1 xs ys}
       -> xs0 <= ys0
       -> [ xs0 ++ xs1 ]~ xs
       -> [ ys0 ++ ys1 ]~ ys
       -> xs1 <= ys1
       -> xs <= ys
  (x ^- th) +[ p < .x ,- q ]+ ph = x ^- (th +[ p < q ]+ ph)
  (x ,- th) +[ .x ,- p < .x ,- q ]+ ph = x ,- (th +[ p < q ]+ ph)
  [] +[ [] < [] ]+ ph = ph

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

  klex-append : {ss0 ss1 ss : List S}{ts : List T}
             -> [ ss0 ++ ss1 ]~ ss
             -> [ klex ss0 ++ klex ss1 ]~ ts
             -> klex ss ~ ts
  klex-append [] [] = r~
  klex-append (_,-_ {xs} {zs = zs} x p) q
    with _ , r <- append (f x) (klex xs)
    with _ , u <- append (f x) (klex zs)
    with _ , s , t <- asso++13 r q
    with r~ <- klex-append p t
    with r~ <- append! (_ , u) (_ , s)
       = r~

  klex-append' : {ss0 ss1 ss : List S}
             -> [ ss0 ++ ss1 ]~ ss
             -> [ klex ss0 ++ klex ss1 ]~ klex ss
  klex-append' {ss0} {ss1} p
    with _ , q <- append (klex ss0) (klex ss1)
    with r~ <- klex-append p q
    = q


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

module _ {l v : Nat}(x : List (List (Chunk l v) * List (Chunk l v))) where

  data `Thin : List (Chunk l v) -> List (Chunk l v) -> Set where
    `drop : (c : Chunk l v) -> `Thin       []  (c ,- [])
    `[]   : `Thin [] []
    _`+[_<_]+_ : forall {cs0 ds0 cs1 ds1 cs ds}
         -> `Thin cs0 ds0
         -> [ cs0 ++ cs1 ]~ cs
         -> [ ds0 ++ ds1 ]~ ds
         -> `Thin cs1 ds1
         -> `Thin cs ds
    `id : forall {cs} -> `Thin cs cs
    _`-<_ : forall {cs ds es} -> `Thin cs ds -> `Thin ds es -> `Thin cs es
    `# : forall {cs ds} -> ((cs , ds) ,- []) <= x -> `Thin cs ds

module _ {l v : Nat}{x : List (List (Chunk l v) * List (Chunk l v))}
  {X : Set}(rh : All (kk X) l)(sg : All (kk (List X)) v)
  where

  lev : List (Chunk l v) -> List X
  lev = klex (chunkEval rh sg)

  module _ (ch : All (\ (cs , ds) -> lev cs <= lev ds) x)
    where

    thinEval : forall {cs ds} -> `Thin x cs ds -> lev cs <= lev ds
    thinEval (`drop c) = no
    thinEval `[] = []
    thinEval (th `+[ p < q ]+ ph) =
      thinEval th
      +[ klex-append' _ p < klex-append' _ q ]+
      thinEval ph
    thinEval `id = io
    thinEval (th `-< ph) = thinEval th -< thinEval ph
    thinEval (`# i) = only (i <? ch)


module _ {l v : Nat}{x : List (List (Chunk l v) * List (Chunk l v))} where

  data `ThinPrime : List (Chunk l v) -> List (Chunk l v) -> Set where
    `drop : (c : Chunk l v) -> `ThinPrime       []  (c ,- [])
    `keep : (c : Chunk l v) -> `ThinPrime (c ,- []) (c ,- [])
    


    {-
    PLAN:

    We need to identify a notion of *prime* thinning such that
    primes are only trivially decomposable with tensor.

    Our normal form is then a tensor of primes.

    Primeness is all about awkward compositions. Compositions
    only fail to compute out because of free variables. They're
    prime when there is failure of alignment.

    We should also ensure that we eta away thinnings
    with empty wee ends.
    -}
