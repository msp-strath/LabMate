{- LANGUAGE TupleSections #-}

module BRect where

data BR = BR {wid :: Int, hei :: Int} deriving (Show, Eq)

-- make sure the BRs have strictly decreasing width
-- and strictly increasing height
type Narrow x = [(BR, x)]

insertNarrow :: (BR, x) -> Narrow x -> Narrow x
insertNarrow bx [] = [bx]
insertNarrow bx@(BR bw bh, _) n@(cx@(BR cw ch, _) : n') =
  case compare bw cw of
    LT -> if bh <= ch then insertNarrow bx n else cx : insertNarrow bx n'
    EQ -> if bh < ch then bx : n' else n
    GT -> if bh < ch then bx : n  else n

mergeNarrow :: Narrow x -> Narrow x -> Narrow x
mergeNarrow [] n = n
mergeNarrow n [] = n
mergeNarrow n@(bx@(BR bw bh, _) : n') m@(cx@(BR cw ch, _) : m') =
  case (compare bw cw, compare bh ch) of
    (LT, GT) -> cx : mergeNarrow n m'
    (LT, _ ) -> mergeNarrow n m'
    (EQ, LT) -> bx : mergeNarrow n' m'
    (EQ, _ ) -> cx : mergeNarrow n' m'
    (GT, LT) -> bx : mergeNarrow n' m
    (GT, _ ) -> mergeNarrow n' m

data HVT
  = W String
  | (BR, HVT) :||: (BR, HVT)
  | (BR, HVT) :==: (BR, HVT)
  | P (BR, HVT)

(-!) :: Int -> Int -> Int
x -! y = max 0 (x - y)

instance Show HVT where
  show = unlines . render

render :: HVT -> [String]
render (W x) = [x]
render ((ld, lt) :||: (rd, rt)) = zipWith (\ l r -> l ++ " " ++ r)
  (render lt ++ replicate (hei rd - hei ld) (replicate (wid ld) ' '))
  (render rt ++ replicate (hei ld - hei rd) (replicate (wid rd) ' '))
render ((td, tt) :==: (bd, bt)) =
  map (++ replicate (wid bd - wid td) ' ') (render tt) ++
  map (++ replicate (wid td - wid bd) ' ') (render bt)
render (P (xd, xt)) =
  zipWith (++) (lpar (hei xd)) $ zipWith (++) (render xt) (rpar (hei xd))
  where
    lpar h = "(" : replicate (h - 1) "|"
    rpar h = replicate (h - 1) "|" ++ [")"]

wordy :: String -> (BR, HVT)
wordy x = (BR {wid = length x, hei = 1}, W x)

(<||>) ::  (BR, HVT) -> (BR, HVT) -> (BR, HVT)
l@(ld, _) <||> r@(rd, _) =
  ( BR {wid = wid ld + 1 + wid rd, hei = max (hei ld) (hei rd)}
  , l :||: r
  )

(<==>) ::  (BR, HVT) -> (BR, HVT) -> (BR, HVT)
t@(td, _) <==> b@(bd, _) =
  ( BR {wid = max (wid td) (wid bd), hei = hei td + hei bd}
  , t :==: b
  )

paren :: (BR, HVT) -> (BR, HVT)
paren x@(xd, _) =
  ( BR {wid = 2 + wid xd, hei = hei xd}
  , P x
  )

horiz :: Narrow HVT -> Narrow HVT -> Narrow HVT
horiz [x] ys = map (x <||>) ys
horiz xs [y] = map (<||> y) xs
horiz (x@(xd, _) : xs) (y@(yd, _) : ys) = insertNarrow (x <||> y) $
  case compare (hei xd) (hei yd) of
    LT -> horiz xs (y : ys)
    EQ -> horiz xs ys
    GT -> horiz (x : xs) ys
horiz _ _ = []

verti :: Narrow HVT -> Narrow HVT -> Narrow HVT
verti [x] ys = map (x <==>) ys
verti xs [y] = map (<==> y) xs
verti (x@(xd, _) : xs) (y@(yd, _) : ys) = insertNarrow (x <==> y) $
  case compare (wid xd) (wid yd) of
    LT -> verti (x : xs) ys
    EQ -> verti xs ys
    GT -> verti xs (y : ys)
verti _ _ = []

data BRect
  = BRect {righty :: Narrow HVT, downy :: Narrow HVT}
  deriving Show

instance Semigroup BRect where
  x <> y = BRect
    { righty = horiz (righty x) ys
    , downy = mergeNarrow
        (verti (righty x) ys)
        (verti (downy x) ys)
    }
    where ys = mergeNarrow (righty y) (downy y)

par :: BRect -> BRect
par x = BRect
  { righty = mergeNarrow (map paren (righty x)) (map paren (downy x))
  , downy = []
  }

word :: String -> BRect
word x = BRect
  { righty = [wordy x]
  , downy = []
  }

brect :: Int -> BRect -> IO ()
brect w x = go (mergeNarrow (righty x) (downy x)) where
  go [(_,x)] = putStrLn (show x)
  go (x@(d, t) : xs) = if wid d > w then go xs else putStr (show t)
