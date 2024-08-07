{-# LANGUAGE LiberalTypeSynonyms #-}
module MissingLibrary where

import Control.Arrow ((***))

class Monoid m => PullbackMonoid m where
  mpullback :: m -> m -> (m, (m, m))
{-
  mpullback x y = (p, (px, py)),
  such that x = p <> px
            y = p <> py
  and for p', px', py', such that
  x = p' <> px' and y = p' <> py',
  there is some m, such that
    p   = p' <> m
    px' = m <> px
    py' = m <> py
-}

instance Eq x => PullbackMonoid [x] where
  mpullback (x:xs) (y:ys)
    | x == y = ((x:) *** id) (mpullback xs ys)
  mpullback xs ys = ([], (xs, ys))

data Varying a = VaryNone | VaryOne a Integer | VaryTons
  deriving (Show, Eq, Ord)

instance Eq a => Monoid (Varying a) where
  mempty = VaryNone
  mappend VaryNone x = x
  mappend x VaryNone = x
  mappend VaryTons _ = VaryTons
  mappend _ VaryTons = VaryTons
  mappend (VaryOne a n) (VaryOne b k) | a == b = VaryOne a (n + k)
                                      | otherwise = VaryTons

instance Eq a => Semigroup (Varying a) where
  (<>) = mappend

type (-:>) s t i = s i -> t i
infixr 0 -:>


type All p = forall i . p i

class IxFunctor (f :: (i -> *) -> (o -> *)) where
  ixmap :: All (s -:> t) -> All (f s -:> f t)
