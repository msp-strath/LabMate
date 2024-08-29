module MissingLibrary
  (PullbackMonoid(..)
  , Bag, bag, sortBag, bagSize, fritz
  ) where

import Data.List
import Data.Either
import Data.Monoid
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

-- List should always be sorted
newtype Bag x = Bag [x]
  deriving (Show, Eq)

bag :: Ord x => [x] -> Bag x
bag xs = Bag (sort xs)

sortBag :: Ord x => Bag x -> [x]
sortBag (Bag xs) = xs

bagSize :: Bag x -> Int
bagSize (Bag xs) = length xs

fritz :: Bag (Either a b) -> (Bag a, Bag b)
fritz (Bag xs) = (Bag *** Bag) $ partitionEithers xs

instance Ord x => Monoid (Bag x) where
  mempty = Bag []
  Bag xs `mappend` Bag ys = Bag (merge xs ys)
    where
      merge [] ys = ys
      merge xs [] = xs
      merge (x:xs) (y:ys) = if x <= y then x:merge xs (y:ys) else y:merge (x:xs) ys

instance Ord x => Semigroup (Bag x) where
  (<>) = mappend

instance PullbackMonoid (Sum Int) where
  mpullback (Sum n) (Sum m) = if n < m then (Sum n, (Sum 0, Sum (m-n))) else (Sum m, (Sum (n-m), Sum 0))

instance Ord x => PullbackMonoid (Bag x) where
  mpullback (Bag xs) (Bag ys) = (Bag ps, (Bag xs', Bag ys')) where
    (ps, (xs', ys')) = go xs ys

    go [] ys = ([], ([], ys))
    go xs [] = ([], (xs, []))
    go (x:xs) (y:ys) = case compare x y of
      LT -> let (ps, (xs', ys')) = go xs (y:ys) in (ps, (x:xs', ys'))
      EQ -> let (ps, (xs', ys')) = go xs ys in (x:ps, (xs', ys'))
      GT -> let (ps, (xs', ys')) = go (x:xs) ys in (ps, (xs', y:ys'))
