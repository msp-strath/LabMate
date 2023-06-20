module Term.Indexed where

data (==) :: a -> a -> * where
  Refl :: x == x

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

newtype Flip (f :: b -> a -> *) (x :: a) (y :: b) =
  Flip {getFlip :: f y x}

newtype Konst (x :: *) (y :: b) = Konst {getKonst :: x}

instance Show x => Show (Konst x y) where
  show = show . getKonst