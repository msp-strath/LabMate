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
