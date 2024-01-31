{-# LANGUAGE QuantifiedConstraints, UndecidableInstances #-}
module Term ( module Term
            , module Term.Indexed
            , module Term.Natty
            , module Term.Thinning
            , module Term.Vec) where
import Term.Indexed
import Term.Natty
import Term.Thinning
import Term.Vec
import Hide
import Bwd
import Data.Set (Set)
import qualified Data.Set as Set

import Debug.Trace
import Data.List (intercalate)
import MissingLibrary

truck = const id

data Sort
  = Syn
  | Chk
  | One
  | Prd Sort Sort
  | Sub Nat  -- the source scope of the substitution
  deriving (Eq, Show)

data Ctor (s :: Sort) (t :: Sort) where
  -- atoms
  A :: String -> Ctor One Chk
  -- integers
  I :: Integer -> Ctor One Chk
  -- string literals
  SL :: String -> Ctor One Chk
  -- double literals
  DL :: Double -> Ctor One Chk
  -- embedding
  E :: Ctor Syn Chk
  -- radicals
  R :: Ctor (Prd Chk Chk) Syn
  -- tuples
  T :: Ctor (Prd Chk Chk) Chk
  -- desctructors
  D :: Ctor (Prd Syn Chk) Syn
  -- metavar usage (these are unknowns, not schematic vars)
  M :: (Name, Natty k) -> Ctor (Sub k) Syn
  -- subst
  S0 :: Ctor One (Sub Z)
  ST :: Ctor (Prd (Sub n) Syn) (Sub (S n))

type Root = Bwd (String, Int)
type NameSupply = (Root, Int)
newtype Name = Name { longname :: [(String, Int)] }
  deriving (Eq, Ord)

localName :: Name -> Name -> String
localName (Name dns) (Name lns) =
  let (_, (px, py)) =  mpullback lns dns
  in (if null px then "" else show (length px) ++ "\\")
     ++ intercalate "." [n ++ show i | (n, i) <- py]

rootNamespace :: Name
rootNamespace = Name [("labmate", 0)]

instance Show Name where
  show (Name ns) = intercalate "." [n ++ show i | (n, i) <- ns]

name :: NameSupply -> String -> Name
name (r, n) s = Name $ r <>> [(s, n)]

data Term (s :: Sort)
          (n :: Nat)     -- object variable support
  where
  -- the object var
  V :: Term Syn (S Z)
  -- empty tuple
  U :: Term One Z
  -- pairing
  P :: Term a l -> Cov l r n -> Term b r -> Term (Prd a b) n
  -- constant function
  K :: Term Chk n -> Term Chk n
  -- relevant function
  L :: Hide String -> Term Chk (S n) -> Term Chk n
  -- strictness annotation to shut the coverage checker up
  (:$) :: !(Ctor s t) -> Term s n -> Term t n

-- for documentary purposes; used only when we *know* (and not merely
-- hope) a term is a type, a normalised type or a canonical form,
-- respectively
type Type = Term Chk
type NmTy = Type
type Norm = Term

---------------------------------------------
type Context n = Vec n (String, Type ^ n)

emptyContext :: Context Z
emptyContext = VN

infixl 5 \\\

(\\\) :: Context n -> (String, Type ^ n) -> Context (S n)
ctx \\\ x = fmap wk <$> (ctx :# x)

---------------------------------------------
cmpCtor :: Ctor s t -> Ctor s' t -> Ordering' (s == s')
cmpCtor (A s) (A s') = fromOrd Refl $ compare s s'
cmpCtor (I i) (I i') = fromOrd Refl $ compare i i'
cmpCtor (SL s) (SL s') = fromOrd Refl $ compare s s'
cmpCtor (DL d) (DL d') = fromOrd Refl $ compare d d'
cmpCtor E E = EQ' Refl
cmpCtor R R = EQ' Refl
cmpCtor T T = EQ' Refl
cmpCtor D D = EQ' Refl
cmpCtor (M (n, k)) (M (n', k')) = case truck ("MetaCmp " ++ show n ++" =?= " ++ show n') $ compare n n' of
  LT -> LT'
  GT -> GT'
  EQ -> (\Refl -> Refl) <$> cmpNatty k k'
cmpCtor S0 S0 = EQ' Refl
cmpCtor ST ST = EQ' Refl
cmpCtor t t' = case compare (helper t) (helper t') of
  LT -> LT'
  GT -> GT'
  EQ -> error "cmpCtor::IMPOSSIBLE"
  where
    helper :: Ctor s t -> Integer
    helper = \case
      { A{} -> 1; I{} -> 2; E -> 3; R -> 4
      ; T -> 5; D -> 6; M{} -> 7; S0 -> 8
      ; ST{} -> 9; SL{} -> 10; DL{} -> 11 }


-- these instances should only be used for Norm
instance Eq (Norm s n) where
  t == t' = compare t t' == EQ

instance Ord (Norm s n) where
  compare  V         V        = EQ
  compare  U         U        = EQ
  compare (P l u r) (P l' u' r') = case cmpCov u u' of
    LT' -> LT
    GT' -> GT
    EQ' (Refl, Refl) -> compare (l, r) (l', r')
  compare (K t)     (K t')    = compare t t'
  compare (L _ t)   (L _ t')  = compare t t'
  compare (c :$ t)  (c':$ t') = case cmpCtor c c' of
    LT' -> LT
    GT' -> GT
    EQ' Refl -> compare t t'
  compare t1 t2 = compare (helper t1) (helper t2)
    where
       helper :: Term s n -> Integer
       helper = \case
         { V{} -> 0; U{} -> 1; P{} -> 2;
         ; K{} -> 3; L{} -> 4; (:$){} -> 6 }

--------------- smart ctors ---------------
var :: S Z <= n -> Term Syn ^ n
var = (V :^)

evar :: S Z <= n -> Term Chk ^ n
evar = (E $^). var

atom :: NATTY n => String -> Term Chk ^ n
atom s = (A s :$ U) :^ no natty

pattern Atom :: () => (s ~ Chk) => String -> Term s ^ n
pattern Atom s <- A s :$ U :^ _

nil :: NATTY n => Term Chk ^ n
nil = atom ""

pattern Nil :: () => (s ~ Chk) => Term s ^ n
pattern Nil <- Atom ""

nilEh :: Term s ^ n -> Maybe ()
nilEh (A "" :$ U :^ _) = Just ()
nilEh _ = Nothing

class Literal t where
  ctor :: t -> Ctor One Chk

lit :: (Literal t, NATTY n) => t -> Term Chk ^ n
lit t = (ctor t :$ U) :^ no natty

instance Literal Integer where ctor = I
instance Literal Int     where ctor = I . toInteger
instance Literal Double  where ctor = DL
instance Literal String  where ctor = SL

pattern Intg :: () => (s ~ Chk) => Integer -> Term s ^ n
pattern Intg i <- I i :$ U :^ _

infixr 5 <&>
(<&>) :: Term s ^ n -> Term t ^ n -> Term (Prd s t) ^ n
(tl :^ th) <&> (tr :^ ph) | u :^ ps <- cop th ph = P tl u tr :^ ps

split :: Term (Prd a b) ^ n -> (Term a ^ n, Term b ^ n)
split (P tl u tr :^ ph) = (tl :^ covl u -< ph, tr :^ covr u -< ph)

infixr 5 $^
($^) :: Ctor s t -> Term s ^ n -> Term t ^ n
c $^ (t :^ th) = (c :$ t) :^ th

($?) :: Ctor s t -> Term t ^ n -> Maybe (Term s ^ n)
c $? (c' :$ t :^ th) | EQ' Refl <- cmpCtor c c' = Just (t :^ th)
c $? _ = Nothing

-- if we don't now that we are in Chk, we cannot really ask for
-- canonical pairs
pairEh :: Term Chk ^ n -> Maybe (Term Chk ^ n, Term Chk ^ n)
pairEh t = split <$> T $? t

lam :: String -> Term Chk ^ S n -> Term Chk ^ n
lam _ (t :^ No th) = K t :^ th
lam x (t :^ Su th) = L (Hide x) t :^ th

lamEh :: Term s ^ n -> Maybe (Term Chk ^ S n)
lamEh = (snd <$>) . lamNameEh

lamNameEh :: Term s ^ n -> Maybe (String, Term Chk ^ S n)
lamNameEh (K t :^ th) = Just ("_", t :^ No th)
lamNameEh (L (Hide x) t :^ th) = Just (x, t :^ Su th)
lamNameEh _ = Nothing

subst :: NATTY n => Vec k (Term Syn ^ n) -> Subst k ^ n
subst VN = Sub0 :^ no natty
subst (tz :# (t :^ ph))
  | sig :^ th <- subst tz
  , u   :^ ps <- cop th ph
  = SubT sig u t :^ ps

meta :: NATTY n => (Name, Natty k) -> Vec k (Term Syn ^ n) -> Term Syn ^ n
meta m tz | sig :^ th <- subst tz = M m :$ sig :^ th

pattern FreeVar :: (s ~ Chk, n ~ Z) => Name -> Term s ^ n
pattern FreeVar s = E :$ (M (s, Zy) :$ Sub0) :^ Ze

wrapMeta :: NATTY n => Name -> Term Chk ^ n
wrapMeta x = let n = natty in E $^ M (x, n) $^ (idSubst n :^ io n)

tup :: NATTY n => [Term Chk ^ n] -> Term Chk ^ n
tup = foldr (\x y -> T $^ x <&> y) nil

tupEh :: Term Chk ^ n -> Maybe [Term Chk ^ n]
tupEh t | Just () <- nilEh t = Just []
tupEh t = do
  (h, t) <- pairEh t
  (h :) <$> tupEh t

type Tag = String

tag :: NATTY n => Tag -> [Term Chk ^ n] -> Term Chk ^ n
tag s ts = tup $ atom s : ts

tagEh :: Term Chk ^ n -> Maybe (Tag, [Term Chk ^ n])
tagEh (A s :$ U :^ _) = Just (s, [])
tagEh t = case tupEh t of
  Just ((A s :$ U :^ _) : ts) -> Just (s, ts)
  _   -> Nothing

-------------------------------------------

type Subst k = Term (Sub k)

{-# COMPLETE Sub0, SubT #-}

pattern Sub0 :: () => (k ~ Z, n ~ Z) => Subst k n
pattern Sub0 = S0 :$ U

pattern SubT :: () => (k ~ S j)
             => Subst j l
             -> Cov l r n
             -> Term Syn r
             -> Subst k n
pattern SubT l u r = ST :$ P l u r

substSrc :: Subst k n -> Natty k
substSrc Sub0 = Zy
substSrc (SubT t _ _) = Sy (substSrc t)

substSupport :: Subst k n -> Natty n
substSupport Sub0 = Zy
substSupport (SubT _ u _) = bigEnd (covl u)

wkSubst :: Subst k n -> Subst (S k) (S n)
wkSubst sig = SubT sig (NS (lCov (substSupport sig))) V

idSubst :: Natty n -> Subst n n
idSubst Zy = S0 :$ U
idSubst (Sy n) = wkSubst (idSubst n)

idSubstEh :: Subst k n -> Either (Positive k) (k == n)
idSubstEh Sub0 = Right Refl
idSubstEh (SubT sig (NS u) V) | Refl <- allRight (swapCov u) = case idSubstEh sig of
  Left (IsSy n) -> Left $ IsSy (Sy n)
  Right Refl -> Right Refl
idSubstEh (SubT t _ _) = Left (IsSy (substSrc t))

sub0 :: Term Syn ^ n -> Subst (S n) ^ n
sub0 tm@(_ :^ th) = let n = bigEnd th in
  subSnoc (idSubst n :^ io n) tm

subSnoc :: Subst k ^ n -> Term Syn ^ n -> Subst (S k) ^ n
subSnoc sig tm = ST $^ sig <&> tm

tmShow :: forall s n
       .  Bool         -- is the term a cdr
       -> Term s ^ n
       -> (Name, Vec n String) -- pair of a local namespace and the
                               -- names of all vars in scope
       -> String
tmShow b (V :^ th) (_, ctx) = barIf b ++ vonly (th ?^ ctx)
tmShow b Nil _
  | b = ""
  | otherwise = "[]"
tmShow b (A s :$ U :^ _) _ = barIf b ++ "'" ++ s
tmShow b (I i :$ U :^ _) _ = barIf b ++ show i
tmShow b (U :^ _) _ = ""
tmShow b (P tl u tr :^ th) _ = "tmShow: not in a great spot"
tmShow b (K tm :^ th) ctx = barIf b ++ "(\\_. " ++ tmShow b (tm :^ th) ctx ++ ")"
tmShow b (L (Hide nm) tm :^ th) (ns, ctx) = concat [barIf b, "(\\", x, ". ", tmShow False (tm :^ Su th) (ns, ctx :# x), ")"]
  where
    x = head $ filter (not . (`elem` ctx)) (nm : [nm ++ show i | i <- [0..]])
tmShow b (E :$ t :^ th) ctx = tmShow b (t :^ th) ctx
tmShow b (R :$ t :^ th) ctx =
  concat [barIf b, "(", tmShow False tm ctx, " : ", tmShow False ty ctx, ")"]
    where (tm, ty) = split (t :^ th)
tmShow b (M (m, _) :$ sig :^ th) (ns, ctx) = barIf b ++ localName m ns ++ case idSubstEh sig of
  Left (IsSy n) -> case sig of
    SubT sig u t -> concat ["{", substShow (sig :^ covl u -< th) ctx, tmShow False (t :^ covr u -< th) (ns, ctx), "}"]
  Right Refl -> ""
  where
    substShow :: forall j n . Subst j ^ n -> Vec n String -> String
    substShow (Sub0 :^ _) _ = ""
    substShow (SubT sig u t :^ th) ctx = concat [substShow (sig :^ covl u -< th) ctx, tmShow False (t :^ covr u -< th) (ns, ctx), ", "]
tmShow b (T :$ P tl u tr :^ th) ctx =
  if b then " " ++ s else "[" ++ s ++ "]"
  where
    s = tmShow False (tl :^ covl u -< th) ctx ++ tmShow True (tr :^ covr u -< th) ctx
tmShow b (D :$ tm :^ th) ctx = let (a, d) = split (tm :^ th)
  in concat [barIf b, tmShow False a ctx, "(", tmShow False d ctx, ")"]
-- TODO : add the remaining cases

barIf :: Bool -> String
barIf True = " | "
barIf False = ""

instance NATTY n => Show (Term s ^ n) where
  show t = tmShow False t (rootNamespace, names natty)

data Roof :: Nat -> Nat -> Nat -> * where
  Roof :: Subst l l' -> Cov l' r' n -> Subst r r' -> Roof l r n

roofLemma :: Cov l r k -> Subst k n -> Roof l r n
roofLemma ZZ Sub0 = Roof Sub0 ZZ Sub0
roofLemma (SN u0) (SubT sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , u3 :^\^: u4 <- rotateRCov (swapCov u2) u1
  = Roof (SubT sigl u4 t) (swapCov u3) sigr
roofLemma (NS u0) (SubT sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , u3 :^\^: u4 <- rotateRCov u2 u1
  = Roof sigl u3 (SubT sigr u4 t)
roofLemma (SS u0) (SubT sig u1 t)
  | Roof sigl u2 sigr <- roofLemma u0 sig
  , MiddleFour u3 u4 u5 <- middleFour u2 u1 (allCov (weeEnd (covr u1)))
  = Roof (SubT sigl u3 t) u4 (SubT sigr u5 t)

class Substable (t :: Nat -> *) where

  (//) :: t k -> Subst k n -> t n
  t // sig = case idSubstEh sig of
    Left (IsSy _) -> t /// sig
    Right Refl -> t

  -- substWorker
  (///) :: t (S k)
        -> Subst (S k) n -- must not be the id subst
        -> t n

instance Substable (Term s) where

  V /// (SubT Sub0 u t) | Refl <- allRight u = t
  P tl u tr /// sig | Roof sigl u' sigr <- roofLemma u sig =
    P (tl // sigl) u' (tr // sigr)
  K t /// sig = K (t /// sig)
  L x t /// sig = L x (t /// wkSubst sig)
  (c :$ t) /// sig = c :$ (t /// sig)


(//^) :: Term s ^ k -> Subst k ^ n -> Term s ^ n
(t :^ th) //^ (sig :^ ph) | Roof sigl u sigr <- roofLemma (rightAll th) sig =
  t // sigl :^ covl u -< ph

class Mk t where
  type Scope t :: Nat
  type Uncurry t :: *

  from :: (Uncurry t -> Term Chk ^ Scope t, (Uncurry t -> Term Chk ^ Scope t) -> t)

  mk :: t
  mk = k f where (f, k) = from

instance (NATTY n) => Mk (Term Chk ^ n) where
  type Scope (Term Chk ^ n) = n
  type Uncurry (Term Chk ^ n) = ()
  from = (\() -> nil, ($ ()))

instance (Mk t, NATTY (Scope t)) => Mk (String -> t) where
  type Scope (String -> t) = Scope t
  type Uncurry (String -> t) = (String, Uncurry t)
  from = (\(a, s) -> T $^ (atom a <&> g s), \f a -> k (\s -> f (a, s)))
    where (g, k) = from

instance (Mk t, NATTY n, Scope t ~ n) => Mk (Term Chk ^ n -> t) where
  type Scope (Term Chk ^ n -> t) = n
  type Uncurry (Term Chk ^ n -> t) = (Term Chk ^ n, Uncurry t)
  from = (\(a, s) -> T $^ (a <&> g s), \f a -> k (\s -> f (a, s)))
    where (g, k) = from

instance (Mk t, NATTY n, Scope t ~ n) => Mk (Term Syn ^ n -> t) where
  type Scope (Term Syn ^ n -> t) = n
  type Uncurry (Term Syn ^ n -> t) = (Term Syn ^ n, Uncurry t)
  from = (\(a, s) -> T $^ (E $^ a) <&> g s, \f a -> k (\s -> f (a, s)))
    where (g, k) = from

foo0 :: Term Chk ^ S (S (S Z))
foo0 = mk

foo1 :: Term Chk ^ S (S (S Z))
foo1 = mk "Foo"  -- produces `T $^ atom "Foo" <&> nil` , *not* `atom "Foo"`

foo2 :: Term Chk ^ S (S (S Z))
foo2 = mk "Foo" (var 0)

foo3 :: Term Chk ^ S (S (S Z))
foo3 = mk "Foo" (var 0) (var 2)

theTerm :: Term Chk ^ S (S (S Z))
theTerm = lam "w" $ mk (evar 0) (evar 2) (evar 3)

theNames :: Vec (S (S (S Z))) String
theNames = VN :# "z" :# "y" :# "x"

testShow :: Term Chk ^ S (S (S Z)) -> IO ()
testShow t = putStrLn $ tmShow False t (rootNamespace, theNames)

-- computig deBruijn levels
names :: Natty n -> Vec n String
names Zy = VN
names (Sy n) = names n :# ("#" ++ show n)

class Dependencies t where
  dependencies :: t -> Set Name

instance Dependencies (Ctor s t) where
  dependencies (M (x, _)) = Set.singleton x
  dependencies _          = mempty

instance Dependencies (Term s n) where
  dependencies (c :$ t) = dependencies c <> dependencies t
  dependencies (P l _ r) = dependencies l <> dependencies r
  dependencies (K t) = dependencies t
  dependencies (L _ t) = dependencies t
  dependencies _ = mempty

instance Dependencies x => Dependencies (Vec n x) where
  dependencies = foldMap dependencies

instance (forall n . Dependencies (x n)) => Dependencies (x ^ n) where
  dependencies (t :^ _) = dependencies t
