module ThinExp where

type Name = String

data ListChunk
  = E Int  -- Element
  | N Name -- NeutralList
  deriving (Show, Eq)

type ListValue = [ ListChunk ]

data ThinStrip
  = Bool :? ListChunk
  | NeutralThin Name
  | ThinValue :- ThinValue
  deriving (Show, Eq)

data ThinChunk = MkThinChunk
  { bigEnd :: ListValue
  , middle :: ThinStrip
  , weeEnd :: ListValue
  }
  deriving (Show, Eq)

type ThinValue = [ ThinChunk ]

type Environment = [ (Name, (ListValue, ListValue)) ]

type Meaning = Environment -> ThinValue

data ListCompare a = MkListCompare
  { longestCommonPrefix :: [a]
  , leftSuffix          :: [a]
  , rightSuffix         :: [a]
  }
  deriving (Show)

data Bwd a = B0 | Bwd a :< a
  deriving (Show, Eq, Functor, Foldable)

type Cursor a = (Bwd a , [a])
type ThinCursor = Cursor ThinChunk

(<>>) :: Bwd a -> [a] -> [a]
xz <>> xs = foldr (:) xs xz

rightPastPost
  :: Eq b
  => (a -> [b]) -- measure
  -> Cursor a   -- c
  -> [b]        -- post, it *must* be a prefix of the concatenated
                -- measures on the right of `c`
  -> ([b]       -- overshoot
     , Cursor a)
rightPastPost _ c [] = ([], c)
rightPastPost m (az, a : as) bs = case listCompare (m a) bs of
  MkListCompare{..}
    | [] <- leftSuffix -> rightPastPost m (az :< a, as) rightSuffix
    | otherwise        -> (leftSuffix, (az :< a, as))

listCompare :: Eq a => [a] -> [a] -> ListCompare a
listCompare (x : xs) (y : ys)
  | x == y = case listCompare xs ys of
      MkListCompare{..} -> MkListCompare
        { longestCommonPrefix = x : longestCommonPrefix
        , ..}
listCompare xs ys = MkListCompare
  { longestCommonPrefix = []
  , leftSuffix = xs
  , rightSuffix = ys
  }

thAll :: ListValue -> Meaning
thAll xs _ =
  [ MkThinChunk
    { bigEnd = [x]
    , middle = True :? x
    , weeEnd = [x]
    }
  | x <- xs ]

thNone :: ListValue -> Meaning
thNone xs _ =
  [ MkThinChunk
    { bigEnd = [x]
    , middle = False :? x
    , weeEnd = []
    }
  | x <- xs ]

thNeutral :: Name -> Meaning
thNeutral s rho = case lookup s rho of
  Nothing -> error "thNeutral: outOfScope"
  Just (big, wee) -> if null wee
    then thNone big rho
    else
      [ MkThinChunk
        { bigEnd = big
        , middle = NeutralThin s
        , weeEnd = wee
        }
      ]

thTensor :: Meaning -> Meaning -> Meaning
thTensor th ph = (++) <$> th <*> ph

thComp :: Meaning -> Meaning -> Meaning
thComp th ph = sync <$> th <*> ph
  where
    sync :: ThinValue -> ThinValue -> ThinValue
    sync [] [] = []
    sync []  _ = error "short top, long bottom"
    sync (th : ths) phs = overbite (weeEnd th) (B0 :< th, ths) (B0, phs)

    overbite
      :: ListValue  -- current overbite
      -> ThinCursor -- bigEnd of the composition
      -> ThinCursor -- weeEnd of the composition
      -> ThinValue
    overbite [] (thz, ths) (phz, phs) = (combine (thz <>> []) (phz <>> [])) ++ sync ths phs
    overbite ys thzs phzs = case rightPastPost bigEnd phzs ys of
      (ys, phzs) -> underbite ys thzs phzs

    underbite
      :: ListValue  -- current underbite
      -> ThinCursor -- bigEnd of the composition
      -> ThinCursor -- weeEnd of the composition
      -> ThinValue
    underbite [] (thz, ths) (phz, phs) = (combine (thz <>> []) (phz <>> [])) ++ sync ths phs
    underbite ys thzs phzs = case rightPastPost weeEnd thzs ys of
      (ys, thzs) -> overbite ys thzs phzs

    combine :: ThinValue -> ThinValue -> ThinValue
    combine ths [] = ths
    combine [MkThinChunk{middle = ths :- phs}] pss = combine ths (sync phs pss)
    combine
      [MkThinChunk{middle = b0 :? m, bigEnd = xs}]
      [MkThinChunk{middle = b1 :? _, weeEnd = zs}] =
        [MkThinChunk{bigEnd = xs, middle = (b0 && b1) :? m, weeEnd = zs}]
    combine ths phs =
      [  MkThinChunk
        { bigEnd = foldMap bigEnd ths
        , middle = ths :- phs
        , weeEnd = foldMap weeEnd phs
        }
      ]

rho =
  [ ("x0", ([N "m0"], [N "n0"])), ("x1", ([N "m1"], [N "n1"]))
  , ("y0", ([N "n0"], [N "l0"])), ("y1", ([N "n1"], [N "l1"]))
  ]

test0 =
  (thNeutral "x0" `thTensor` thNeutral "x1") `thComp`
  (thNeutral "y0" `thTensor` thNeutral "y1") $ rho

test1 =
  (thNeutral "x0" `thComp` thNeutral "y0") `thTensor`
  (thNeutral "x1" `thComp` thNeutral "y1") $ rho

data ThSyntax
  = Var Name
  | Aye ListChunk
  | Naw ListChunk
  | Nil
  | ThSyntax :|: ThSyntax
  | ThSyntax :-: ThSyntax
 deriving (Show, Eq)

infixr 9 :-:
infixr 5 :|:

(|||) :: ThSyntax -> ThSyntax -> ThSyntax
th ||| Nil = th
th ||| ph = th :|: ph

quote :: ThinValue -> ThSyntax
quote = foldr ( (|||) . strip . middle ) Nil
  where
    strip :: ThinStrip -> ThSyntax
    strip (True :? x)     = Aye x
    strip (False :? x)    = Naw x
    strip (NeutralThin x) = Var x
    strip (x :- y)        = quote x :-: quote y
