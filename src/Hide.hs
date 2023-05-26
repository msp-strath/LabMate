{-|
Description: Hiding a value by making it behave like a singleton
-}

module Hide where

-- | Hide adds a layer above a value that lets us make it look
-- like a singleton, but not forget the actual value.
newtype Hide x = Hide {unhide :: x}
  deriving (Functor)

instance Show x => Show (Hide x) where show = show . unhide
instance Eq   (Hide x) where _ == _ = True
instance Ord  (Hide x) where compare _ _ = EQ
