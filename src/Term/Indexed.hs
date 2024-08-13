module Term.Indexed where

import Data.Kind

data (==) :: a -> a -> Type where
  Refl :: x == x

-- `qs` is usually a tuple of equations
data Ordering' eqs = LT' | EQ' eqs | GT'
  deriving Functor

fromOrd :: a -> Ordering -> Ordering' a
fromOrd a = \case
  LT -> LT'
  GT -> GT'
  EQ -> EQ' a

-- existential quantification
data Ex :: (a -> Type) -> Type where
  Ex :: p x -> Ex p

-- .. and universal
data Al :: (a -> Type) -> Type where
  Al :: (forall x. p x) -> Al p

-- pointwise conjunction
data (:*) :: (a -> Type) -> (a -> Type) -> (a -> Type) where
  (:*) :: p n -> q n -> (p :* q) n

infixr 5 :*

-- .. and implication
data (:->) :: (a -> Type) -> (a -> Type) -> (a -> Type) where
  FunI :: (p n -> q n) -> (p :-> q) n

newtype Flip :: (b -> a -> Type) -> a -> b -> Type where
  Flip :: { getFlip :: f y x } -> Flip f x y

newtype Konst :: Type -> b -> Type where
  Konst :: { getKonst :: x } -> Konst x y

instance Show x => Show (Konst x y) where
  show = show . getKonst

ixKI :: {- forall (f :: s -> Type)(g :: s -> Type)(a :: s) . -} f a -> g a -> g a
ixKI = const id
