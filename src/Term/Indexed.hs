module Term.Indexed where

data (==) :: a -> a -> * where
  Refl :: x == x

-- `qs` is usually a tuple of equations
data Ordering' eqs = LT' | EQ' eqs | GT'

fromOrd :: a -> Ordering -> Ordering' a
fromOrd a = \case
  LT -> LT'
  GT -> GT'
  EQ -> EQ' a

-- existential quantification
data Ex :: (a -> *) -> * where
  Ex :: p x -> Ex p

-- .. and universal
data Al :: (a -> *) -> * where
  Al :: (forall x. p x) -> Al p

-- pointwise conjunction
data (:*) :: (a -> *) -> (a -> *) -> (a -> *) where
  (:*) :: p n -> q n -> (p :* q) n

infixr 5 :*

-- .. and implication
data (:->) :: (a -> *) -> (a -> *) -> (a -> *) where
  FunI :: (p n -> q n) -> (p :-> q) n

newtype Flip :: (b -> a -> *) -> a -> b -> * where
  Flip :: { getFlip :: f y x } -> Flip f x y

newtype Konst :: * -> b -> * where
  Konst :: { getKonst :: x } -> Konst x y

instance Show x => Show (Konst x y) where
  show = show . getKonst
