module CoreTT where

import Data.Map(Map)
import qualified Data.Map as Map

import Control.Applicative
import Control.Monad
import Control.Arrow ((***))
import Data.List (stripPrefix)
import NormalForm
import MagicStrings
import Term

import Debug.Trace

track = const id -- track

data Status = Crying | Waiting | Hoping | Abstract | ProgramVar
  deriving (Ord, Eq, Show)

data Meta = forall n. Meta
  { mctxt :: Context n
  , mtype :: Typ ^ n
  , mdefn :: Maybe (Term Chk ^ n)
  , mstat :: Status   -- if mdefn is `Just _` mstat should be only
                      -- `Waiting` or `Hoping`
  }

instance Show Meta where
  show = \case
    Meta{..} -> nattily (vlen mctxt) $
      concat [ "Meta{", show mctxt
             , " , ", show mtype, " , ", show mdefn
             , " , ", show mstat
             , "}"]


type Store = Map Name Meta

emptyStore :: Store
emptyStore = Map.empty

-- TODO: issue lookup requests out rather than asking for store in;
-- use freer monads
newtype TC n x =
 TC { runTC :: Store -> Context n -> Either String x }

instance Functor (TC n) where
  fmap = (<*>) . pure

instance Applicative (TC n) where
  pure = return
  (<*>) = ap

instance Alternative (TC n) where
  empty = fail "TC monad"
  TC f <|> TC g = TC $ \st ga -> case f st ga of
    Left msg -> case g st ga of
      Left msg' -> Left $ msg ++ msg'
      r -> r
    r -> r

instance Monad (TC n) where
  return a = TC $ \st ctx -> pure a
  (TC f) >>= k = TC $ \st ga ->
    f st ga >>= \a -> runTC (k a) st ga

instance MonadFail (TC n) where
  fail  = TC . const . const . Left

must :: MonadFail m => String -> Maybe a -> m a
must _ (Just a) = pure a
must s Nothing = fail $ s ++ " must fail"

typeOf :: (S Z <= n) -> TC n (Typ ^ n)
typeOf i = TC $ \_ -> Right . snd . vonly . (i ?^)

scope :: TC n (Natty n)
scope = TC $ \_ -> Right . vlen

withScope :: (NATTY n => TC n t) -> TC n t
withScope c = do
  n <- scope
  nattily n c

under
  :: (String, Typ ^ n)
  -> TC (S n) a
  -> TC n a -- discharging the bound variable is the caller's problem
under ty (TC f) = TC $ \st ctx -> f st (fmap wk <$> (ctx :# ty))

metaLookup :: Name -> TC n Meta
metaLookup s = TC $ \ st _ -> case s `Map.lookup` st of
  Nothing -> error $ "Meta \"" ++ show s ++ "\" not found."
  Just m -> pure m

typeEh :: Term Chk ^ n -> TC n ()
typeEh ty | Just cts <- tagEh ty = case cts of
  (STwo, [])   -> pure ()
  (SAtom, [])  -> pure ()
  (SType, [])  -> pure ()
  (SChar, [])  -> pure ()
  (SAbel, [t]) -> typeEh t
  (SList, [t]) -> typeEh t
  (SEnum, [t]) -> withScope $
    checkEh (mk SList $ atom SAtom) t
  (SPi, [s, t]) | Just (x, t') <- lamNameEh t -> do
    typeEh s
    under (x, s) $ typeEh t'
  (SSig, [s, t]) | Just (x, t') <- lamNameEh t -> do
    typeEh s
    under (x, s) $ typeEh t'
  (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
    | Just (r, cellTy) <- lamNameEh cellTy
    , Just (c, cellTy) <- lamNameEh cellTy -> withScope $ do
      typeEh rowGenTy
      typeEh colGenTy
      under (r, rowGenTy) $ under (c, wk colGenTy) $ typeEh cellTy
      checkEh (mk SList (tag SAbel [rowGenTy])) rs
      checkEh (mk SList (tag SAbel [colGenTy])) cs
  (SDest, [t]) -> typeEh t
  (SQuantity, [g, v]) -> withScope $ do
    typeEh g
    checkEh (mk SAbel g) v
  (ty, _) -> fail $ "typeEh: unknown type " ++ ty
typeEh ty | Just ty <- E $? ty = withScope $ do
  gotTy <- synthEh ty
  subtypeEh gotTy $ atom SType
typeEh _ = fail "typeEh: not a type"

checkEh
  :: Typ ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -> TC n ()  {- Ty \ni tm -}
checkEh ty tm | Just tm <- E $? tm = do
  gotTy <- synthEh tm
  subtypeEh gotTy ty
checkEh ty tm = do
  wantTy <- typeEval ty
  isCanon <- checkCanEh wantTy tm
  if isCanon then pure ()
             else fail "checkEh: no"

checkCanEh
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -> TC n Bool {- Ty \ni tm -}
checkCanEh ty tm | Just x <- tagEh ty = withScope $ case x of
  (SAbel, [genTy]) -> case tupEh tm of
    Nothing | Intg _ <- tm -> checkCanEh genTy nil
    Just []  -> pure True
    Just [Eone, t] -> True <$ checkEh genTy t
    Just [Eplus, s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [Intg _, t] -> True <$ checkEh ty t
    _ -> pure False
  (SList, [genTy]) -> case tupEh tm of
    Nothing | Intg i <- tm ->
      if i >= 0 then checkCanEh genTy nil
      else fail "checkCanEh: negative length list."
    Just []  -> pure True
    Just [Eone, t] -> True <$ checkEh genTy t
    Just [Eplus, s, t] -> True <$ checkEh ty s <* checkEh ty t
    Just [Intg i, t] -> propEh genTy >>= \case
      True | i >= 0 ->  True <$ checkEh ty t
      _ -> fail $ "checkCanEh: " ++
       (if i < 0 then "negative length list"
        else "scalar multiplication at non-prop type")
    _ -> pure False
  (SEnum, [as]) -> do
    nfs <- termToNFList (atom SAtom) as
    True <$ checkEnumEh nfs tm
  (STwo, []) | Intg i <- tm, i == 0 || i == 1 -> pure True
  (SChar, []) | Intg i <- tm, i >= 0 && i <= 128 -> pure True
  (SAtom, []) | Atom _ <- tm -> pure True
  (SPi, [s, t]) | Just t' <- lamEh t, Just (x, tm') <- lamNameEh tm ->
    True <$ under (x, s) (checkEh t' tm')
  (SSig, [s, t]) | Just t' <- lamEh t, Just (a, d) <- pairEh tm -> withScope $ do
    checkEh s a
    True <$ checkEh (t' //^ sub0 (R $^ a <&> s)) d
  (SType, []) -> True <$ typeEh tm
  (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
    | Just cellTy <- lamEh cellTy
    , Just cellTy <- lamEh cellTy -> do
      ((rs', _), (_, cs')) <- checkCanMatrixEh (rowGenTy, colGenTy, cellTy) (rs, cs) tm
      True <$ unnil (mk SAbel rowGenTy) rs' <* unnil (mk SAbel colGenTy) cs'
  _ -> pure False
checkCanEh _ _ = pure False

type Corner n =
  ( Term 'Chk ^ n -- rowHeaders vertically on the left
  , Term 'Chk ^ n -- columnHeaders horizontaly on the top
  )

checkCanMatrixEh
  :: (NmTy ^ n, NmTy ^ n, NmTy ^ S (S n))  -- \row col. cellTy
  -> Corner n        -- (rs, cs)
  -> Term 'Chk ^ n
  -> TC n ( Corner n -- (rs1, cs0), down the left and below
          , Corner n -- (rs0, cs1), rightwards and along the top
          )          -- invariant : rs = rs0 + rs1, cs = cs0 + cs1
{-
     <------------cs------------>

 ^   X-----------X------cs1----->
 |   |           |
 |   |           |
 |   |          rs0
 |   |           |
 rs  |           |
 |   X----cs0----X
 |   |
 |  rs1
 |   |
 v   v

-}

checkCanMatrixEh ty@(rowGenTy, colGenTy, cellTy) mx@(rs, cs) tm
  | Just (Sone, [t]) <- tagEh tm = withScope $ do
    (r, rs') <- uncons rowTy rs
    (c, cs') <- uncons colTy cs
    let sig = subSnoc (sub0 (R $^ r <&> rowTy)) (R $^ c <&> colTy)
    checkEh (cellTy //^ sig) t
    pure ((rs', mk Sone c), (mk Sone r, cs'))
  | Just (Shjux, [l, r]) <- tagEh tm = withScope $ do
    ((rs', cs0), rt@(rs0, _)) <- checkCanMatrixEh ty mx l
    ((rs'', cs1), (_, cs''))  <- checkCanMatrixEh ty rt r
    unnil rowTy rs''
    pure ((rs', mk Splus cs0 cs1), (rs0, cs''))
  | Just (Svjux, [t, b]) <- tagEh tm = withScope $ do
    (lb@(_, cs0), (rs0, cs')) <- checkCanMatrixEh ty mx t
    ((rs'', _), (rs1, cs'')) <- checkCanMatrixEh ty lb b
    unnil colTy cs''
    pure ((rs'', cs0), (mk Splus rs0 rs1, cs'))
  | Just tm <- E $? tm = withScope $ tagEh <$> synthEhNorm tm >>= \case
     Just (SMatrix, [rowGenTy', colGenTy', cellTy', rs0, cs0]) |
       Just (r, cellTy') <- lamNameEh cellTy', Just (c, cellTy') <- lamNameEh cellTy' -> do
         -- TODO: allow factors to float between headers and cell types
         subtypeEh rowGenTy' rowGenTy
         subtypeEh colGenTy' colGenTy
         under (r, mk SAbel rowGenTy') $ under (c, wk $ mk SAbel colGenTy') $ subtypeEh cellTy' cellTy
         True <- track "after subtyping" $ pure True
         (rs0, rs1) <- prefixEh rowTy rs0 rs
         True <- track ("row leftovers " ++ show rs1) $ pure True
         (cs0, cs1) <- prefixEh colTy cs0 cs
         True <- track ("col leftovers " ++ show cs1) $ pure True
         pure ((rs1, cs0), (rs0, cs1))
     _ -> fail "checkCanMatrixEh: malformed cell type"
  | otherwise = fail "checkCanMatrixEh: not a valid matrix ctor"
  where
    rowTy = withScopeOf rowGenTy $ mk SAbel rowGenTy
    colTy = withScopeOf colGenTy $ mk SAbel colGenTy

{-
withListAs :: Typ ^ n -> [Term Chk ^ n] -> TC n (Either [NFAbel n] [NFList n])
withListAs ty tms = propEh ty >>= \case
  True  -> Left <$> traverse (termToNFAbel ty) tms
  False -> Right <$> traverse (termToNFList ty) tms
-}

cons :: Term Chk ^ n -> Term Chk ^ n -> Term Chk ^ n
cons x xs = withScopeOf x $ case xs of
  Nil -> mk Sone x
  _ -> tag Splus [mk Sone x, xs]

uncons :: Typ ^ n -> Term Chk ^ n -> TC n (Term Chk ^ n, Term Chk ^ n)
uncons elty xs = withScope $ propEh elty >>= \case
  True  -> termToNFAbel elty xs >>= \case
    t@NFAbel{..} -> do
      guard (nfConst > 0)
      pure  (nil, nfAbelToTerm (t {nfConst = nfConst - 1}))
  False -> termToNFList elty xs >>= \case
    (Right t) : ts -> pure (t, nfListToTerm ts)
    (Left _) : _ -> fail "uncons: stuck head"
    _ -> fail "uncons: empty list"

unnil :: Typ ^ n -> Term Chk ^ n -> TC n ()
unnil elty xs = withScope $ propEh elty >>= \case
  True  -> termToNFAbel elty xs >>= \case
    NFAbel{nfConst = 0, nfStuck = []} -> pure  ()
    _ -> fail "unnil: non-zero number"
  False -> termToNFList elty xs >>= \case
    [] -> pure ()
    _ -> fail "unnil: non-empty list"

listView :: Norm Chk ^ n -> NFList n
listView t = withScopeOf t $ case tagEh t of
  Just ("", []) -> []
  Just (Sone, [x]) -> [Right x]
  Just (Splus, [x, y]) -> listView x ++ listView y
  _ | Just e <- E $? t -> [Left e]
  _ | Intg i <- t -> replicate (fromInteger i) (Right nil)
  _ -> error $ "bad normal list " ++ show t

unviewList :: NATTY n => Typ ^ n -> NFList n -> Norm Chk ^ n
unviewList ty l | all (== Right nil) l, isUnitType ty = lit (length l)
unviewList ty [] = nil
unviewList ty [Right x] = mk Sone x
unviewList ty [Left x] = E $^ x
unviewList ty (x:xs) = mk Splus (unviewList ty [x]) (unviewList ty xs)

abelView :: Norm Chk ^ n -> NFAbel n
abelView tm
  | Intg i  <- tm  = NFAbel { nfConst = i, nfStuck = [] }
  | Nil <- tm  = mempty
  | Just (Sone, [t]) <- tagEh tm = withScopeOf t $ case t of
     Nil -> NFAbel 1 []
     t   -> NFAbel 0 [(mk Sone t, 1)]
  | Just (Splus, [s, t]) <- tagEh tm = abelView s <> abelView t
  | Just [Intg i, t] <- tupEh tm =
      if i == 0 then mempty else (i *) <$> abelView t
  | otherwise = NFAbel 0 [(tm, 1)]

oneType :: NATTY n => Typ ^ n
oneType = tag SAbel [tag SEnum [nil]]

oneTypeZ :: Typ Z
oneTypeZ = case (oneType :: Typ ^ Z) of u :^ Ze -> u

singMatTy :: Typ ^ n -> Typ ^ n
singMatTy c = nattily (scopeOf c) $ mk SMatrix (tag SEnum [nil]) (tag SEnum [nil]) (lam "i" $ lam "j" $ wk (wk c)) (tag Sone [nil]) (tag Sone [nil])

prefixEh
  :: Typ ^ n
  -> Term Chk ^ n -- candidate prefix modulo subtyping
  -> Term Chk ^ n -- whole list
  -> TC n (Term Chk ^ n, Term Chk ^ n) -- (prefix and suffix from whole list)
prefixEh elty pr l = withScope $ propEh elty >>= \case
  True -> do
    pr@NFAbel{nfConst = n, nfStuck = tns} <- termToNFAbel elty pr
    l@NFAbel{nfConst = m, nfStuck = tms}  <- termToNFAbel elty l
    guard $ n <= m
    suffix <- nfAbelToTerm . NFAbel (m - n) <$> must "prefixEh:nfAbelToTerm" (sub tns tms)
    pure (nfAbelToTerm pr, suffix)
  False -> do
    pr <- termToNFList elty pr
    l  <- termToNFList elty l
    pure $ (nfListToTerm *** nfListToTerm) $ splitAt (length pr) l
  where
    sub :: [(Norm Chk ^ n, Integer)]
        -> [(Norm Chk ^ n, Integer)]
        -> Maybe [(Norm Chk ^ n, Integer)]
    sub [] = pure
    sub ((t, n) : tns) = go
      where
       go [] = Nothing
       go (sm@(s, m) : tms) = case compare s t of
        LT -> (sm :) <$> go tms
        GT -> Nothing
        EQ -> case compare n m of
          LT -> ((t, m - n):) <$> sub tns tms
          GT -> Nothing
          EQ -> sub tns tms

checkEnumEh                   -- typechecking op
  :: NFList n                 -- haystack
  -> Term Chk ^ n             -- needle
  -> TC n (Maybe (NFList n))  -- longest guaranteed suffix of the
                              -- haystack, starting with the needle;
                              -- returns Nothing if we cannot put plus
                              -- after.
checkEnumEh ts tm = withScope $ case tagEh tm of
  Just (s, []) -> case ts of
    Right (Atom s') : us ->
      if s == s' then pure (Just ts) else checkEnumEh us tm
    _ -> fail $ "checkEnumEh: position of atom '" ++ s ++ " not determined."
  Nothing | I i :$ U :^ th <- tm -> case ts of
    Right _ : us -> case compare i 0 of
      LT -> fail "checkEnumEh : negative tag index."
      EQ -> pure $ Just ts
      GT -> checkEnumEh us (I (i - 1) :$ U :^ th)
    _ -> fail "checkEnumEh: tag at index not determined."
  Just (Splus, [x, y]) -> do
    Just ts <- checkEnumEh ts x
    checkEnumEh ts y
  -- neutral terms
  _ | Just tm <- E $? tm -> synthEh tm >>= \ty -> do
    subtypeEh ty (tag SEnum [nfListToTerm ts])
    pure Nothing
  _ -> fail "checkEnumEh:"

synthEh
  :: Term Syn ^ n    {- t -}
  -> TC n (Typ ^ n) {- t \in T, T need *not* be normal -}
synthEh (V :^ i) = typeOf i
synthEh tm | Just tm <- R $? tm, (tm, ty) <- split tm =
  ty <$ typeEh ty <* checkEh ty tm
synthEh tm | Just tm <- D $? tm, (tgt, a) <- split tm =
  tagEh <$> synthEhNorm tgt >>= \case
    Just (SPi, [s, t]) | Just t' <- lamEh t -> withScope $ do
      checkEh s a
      pure (t' //^ sub0 (R $^ a <&> s))
    Just (SSig, [s, t])
      | Atom Sfst <- a -> pure s
      | Atom Ssnd <- a, Just t' <- lamEh t -> withScope $ do
        pure (t' //^ sub0 (D $^ tgt <&> atom Sfst))
      | otherwise -> fail "synthEh: unknown projection"
    _ -> fail "synthEh: no"
synthEh _ = fail "synthEh: no"

synthEhNorm :: Term Syn ^ n {- t -} -> TC n (NmTy ^ n) {- t \in T -}
synthEhNorm tm = synthEh tm >>= typeEval

isUnitType  :: NmTy ^ n {- Ty -} -> Bool
isUnitType ty = case tagEh ty of
  Just (SAbel, [gen]) | Just (SEnum, [Nil]) <- tagEh gen -> True
  _ -> False

checkNormEval
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Norm Chk ^ n)
checkNormEval wantTy tm | Just tm <- E $? tm = do
  (tm, gotTy) <- evalSynth tm
  gotTy <- typeEval gotTy
  etaExpand tm gotTy wantTy
checkNormEval ty tm | Just tty <- tagEh ty = withScope $ case tty of
  _ | isUnitType ty -> pure nil
  (SType, []) -> typeEval tm
  -- TODO: FIXME use reduced order BDD
  (STwo, []) -> nfBoolToTerm <$> termToNFBool tm
  (SAtom, []) -> pure tm
  (SChar, []) -> pure tm
  (SAbel, [genTy]) -> nfAbelToTerm <$> termToNFAbel genTy tm
  (SList, [genTy]) -> propEh genTy >>= \case
      True  -> nfAbelToTerm <$> termToNFAbel genTy tm
      False -> nfListToTerm <$> termToNFList genTy tm
  (SEnum, [as]) -> termToNFList (atom SAtom) as >>= \x ->
      pure $ case findInEnum tm x of
        Just (i, _)  -> lit i
        -- TODO : handle neutrals, reduce further
        _ -> tm
  (SPi, [s, t])
    | Just t' <- lamEh t
    , Just (x, tm') <- lamNameEh tm ->
        lam x <$> under (x, s) (checkNormEval t' tm')
  (SSig, [s, t])
    | Just  t' <- lamEh t
    , Just (a, d) <- pairEh tm -> do
        a <- checkNormEval s a
        d <- checkEval (t' //^ sub0 (R $^ a <&> s)) d
        pure (T $^ a <&> d)
  (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
    | Just cellTy <- lamEh cellTy, Just cellTy <- lamEh cellTy ->
        withScope $ propEh (mk SAbel rowGenTy) >>= \case
          True -> do
            (nf, _) <- checkEvalMatrixNF termToNFAbel (mk SAbel rowGenTy, mk SAbel colGenTy, cellTy) (rs, cs) tm
            pure $ nfMatrixToTerm nf
          False -> do
            (nf, _) <- checkEvalMatrixNF termToNFList (mk SAbel rowGenTy, mk SAbel colGenTy, cellTy) (rs, cs) tm
            pure $ nfMatrixToTerm nf
  -- TODO: try harder to see whether there is any work to do
  (SQuantity, [genTy, dim]) -> pure tm
  (t, _) -> fail $ "checkNormEval: unknown type " ++ t
checkNormEval _ _ = fail "checkNormEval: no"

checkEval
  :: Typ ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Norm Chk ^ n)
checkEval ty tm = do
  ty <- typeEval ty
  checkNormEval ty tm

typeEval :: Typ ^ n -> TC n (NmTy ^ n)
typeEval ty | Just ty <- tagEh ty = withScope $ case ty of
  (x, []) | x `elem` [SAtom, STwo, SType, SChar] -> pure $ atom x
  (SAbel, [genTy]) -> mk SAbel <$> typeEval genTy
  (SList, [genTy]) -> mk SList <$> typeEval genTy
  (SEnum, [as]) -> mk SEnum <$> checkNormEval (mk SList (atom SAtom)) as
  (SPi, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SPi <$> typeEval s <*> (lam x <$> under (x, s) (typeEval t'))
  (SSig, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SSig <$> typeEval s <*> (lam x <$> under (x, s) (typeEval t'))
  (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
    | Just (r, cellTy) <- lamNameEh cellTy, Just (c,cellTy) <- lamNameEh cellTy -> do
      let rowTy = mk SAbel rowGenTy
      let colTy = mk SAbel colGenTy
      mk SMatrix <$> typeEval rowGenTy
                 <*> typeEval colGenTy
                 <*> (lam r <$> under (r, rowTy) (lam c <$> under (c, wk colTy) (typeEval cellTy)))
                 <*> checkEval (mk SList rowTy) rs
                 <*> checkEval (mk SList colTy) cs
  (SDest, [genTy]) -> mk SDest <$> typeEval genTy
  (SQuantity, [genTy, t]) -> mk SQuantity <$> typeEval genTy <*> checkEval (mk SAbel genTy) t
  (ty, _) -> fail $ "typeEval: unknown type " ++ ty
typeEval ty | Just ty <- E $? ty = fst <$> evalSynth ty
typeEval ty = fail "typeEval: no"

-- there is no guarantee that the returned term is the canonical
-- representative of its eq. class because it is *not* eta-long.
evalSynth :: Term Syn ^ n -> TC n (Term Chk ^ n, Typ ^ n)
evalSynth tm = withScope $ case tm of
  V :^ i -> (E $^ tm,) <$> typeOf i
  tm | Just tm <- R $? tm, (tm, ty) <- split tm -> do
    ty <- typeEval ty
    (, ty) <$> checkNormEval ty tm
  tm | Just tm <- D $? tm, (tgt, dstr) <- split tm -> do
    (tgt, tgtTy) <- evalSynth tgt
    tgtTy <- typeEval tgtTy
    case tagEh tgtTy of
      Just (SPi, [s, t]) | Just t' <- lamEh t -> do
        arg <- checkNormEval s dstr
        let sig = sub0 $ R $^ arg <&> s
        let resTy = t' //^ sig
        (, resTy) <$> case lamEh tgt of
          Just bd -> checkEval resTy (bd //^ sig)
          Nothing
            | Just tgt <- E $? tgt -> pure (E $^ D $^ (tgt <&> arg))
            | otherwise -> error "evalSynth: funny function"
      Just (SSig, [s, t])
        | Atom Sfst <- dstr -> pure . (, s) $ case pairEh tgt of
          Just (a, _) -> a
          Nothing
            | Just tgt <- E $? tgt -> E $^ D $^ (tgt <&> atom Sfst)
            | otherwise -> error "evalSynth: funny pair"
        | Atom Ssnd <- dstr, Just t' <- lamEh t ->  pure $ case pairEh tgt of
          Just (a, d) -> (d,  t' //^ sub0 (R $^ a <&> s))
          Nothing
            | Just tgt <- E $? tgt -> ( E $^ D $^ (tgt <&> atom Ssnd)
                                      , t' //^ sub0 (D $^ tgt <&> atom Sfst))
            | otherwise -> error "evalSynth: funny pair"
      Just (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
        | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy
        , Just (SQuantity, [genTy, dim]) <- tagEh cellTy
        , Atom Sinverse <- dstr -> do
            retDim <- under (r, mk SAbel rowGenTy) $ under (c, mk SAbel (wk colGenTy)) $ checkNormEval (mk SAbel genTy) (tup [lit (-1::Integer), dim])
            let sg = subSnoc (subSnoc (idSubst natty :^ No (No (io natty))) (var 0)) (var 1)
            pure (E $^ D $^ ((R $^ (tgt <&> tgtTy)) <&> dstr), mk SMatrix colGenTy rowGenTy (lam c $ lam r $ mk SQuantity genTy retDim //^ sg) cs rs)
      Just (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
        | Just (r, cellTy) <- lamNameEh cellTy, Just (c, cellTy) <- lamNameEh cellTy
        , Atom Stranspose <- dstr -> do
            let sg = subSnoc (subSnoc (idSubst natty :^ No (No (io natty))) (var 0)) (var 1)
            pure (E $^ D $^ ((R $^ (tgt <&> tgtTy)) <&> dstr), mk SMatrix colGenTy rowGenTy (lam c $ lam r $ cellTy //^ sg) cs rs)
      Just (SMatrix, [rowGenTy, colGenTy, cellTy, rs, cs])
        | Atom Suminus <- dstr ->
            pure (E $^ D $^ ((R $^ (tgt <&> tgtTy)) <&> dstr), tgtTy)
      _ -> fail "evalSynth: eliminator for an unknown type"
  tm | Just tm <- MX $? tm, (lmx, rmx) <- split tm -> do
    (lmx, lmxTy) <- evalSynth lmx
    (rmx, rmxTy) <- evalSynth rmx
    -- TODO: FIXME, compute the cell type from lcellTy, rcellTy
    retTy <- case (tagEh lmxTy, tagEh rmxTy) of
      (Just (SMatrix, [rowGenTy, midGenTy, lcellTy, rs, _]), Just (SMatrix, [_, colGenTy, rcellTy, _, cs])) ->
        pure (mk SMatrix rowGenTy colGenTy lcellTy {- YIKES -} rs cs)
    pure (E $^ MX $^ (R $^ lmx <&> lmxTy) <&> (R $^ rmx <&> rmxTy), retTy)
  tm@(M (x, n) :$ sig :^ th) -> metaLookup x >>= \case
    Meta {..}
      | Just Refl <- nattyEqEh (vlen mctxt) n ->
        let ty = mtype //^ (sig :^ th)
        in case mdefn of
          Nothing -> do
            sig <- evalSubst (fmap (//^ (sig :^ th)) <$> mctxt) (sig :^ th)
            pure (E $^ M (x, n) $^ sig, ty)
          Just defn -> let rad = R $^ (defn //^ (sig :^ th)) <&> ty
                       in track (concat ["Yay! ", show tm, " = ", show rad]) $ evalSynth rad
      | otherwise -> fail "evalSynth: usage of a metavariable at wrong arity"
  _ -> fail "evalSynthEh: no"

evalSubst :: Vec k (String, Typ ^ n) -> Subst k ^ n -> TC n (Subst k ^ n)
evalSubst VN _ = (Sub0 :^) <$> (no <$> scope)
evalSubst (ctx :# (_, ty)) sig | Just sig <- ST $? sig = case split sig of
  (sig, tm) -> do
    sig <- evalSubst ctx sig
    ty  <- typeEval ty
    tm  <- checkNormEval ty (E $^ tm)
    let tm' = case E $? tm of
                Just tm -> tm
                Nothing -> R $^ tm <&> ty
    pure (ST $^ sig <&> tm')

evalSynthNmTy :: Term Syn ^ n -> TC n (Term Chk ^ n, NmTy ^ n)
evalSynthNmTy tm = do
  (tm, ty) <- evalSynth tm
  ty <- typeEval ty
  pure (tm, ty)

-- TODO : handle neutral x
findInEnum :: Term Chk ^ n -> NFList n -> Maybe (Integer, NFList n)
findInEnum x ts = case (tagEh x, ts) of
  (Just (s, []), (Right (Atom s')) : us) ->
    if s == s' then pure (0, ts)
    else do
      (n, ts) <- findInEnum x us
      pure (1 + n, ts)
  (Nothing, (Right _) : us) | I i :$ U :^ th <- x ->
    case compare i 0 of
      LT -> Nothing
      EQ -> pure (0, ts)
      GT -> do
        (n, ts) <- findInEnum (I (i - 1) :$ U :^ th) us
        pure (1 + n, ts)
  (Just (Splus, [x,y]), _) -> do
    (n, ts) <- findInEnum x ts
    (m, ts) <- findInEnum y ts
    pure (n + m, ts)
  _ -> Nothing

indexInEnum :: Integer -> NFList n -> Maybe (Term Chk ^ n)
indexInEnum 0 (Right x: _) = Just x
indexInEnum n (_ : xs) = indexInEnum (n - 1) xs
indexInEnum _ _ = Nothing

termToNFList
  :: Typ ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFList n)
termToNFList ty tm
  | Just tm <- E $? tm = evalSynth tm >>= \(tm, _) -> case E $? tm of
      Just tm -> pure [Left tm]
      Nothing -> termToNFList ty tm
  | Intg i <- tm = withScope $ pure $ replicate (fromInteger i) (Right nil)
  | Strg s <- tm = withScope $ pure $ [Right (SL s :$ U :^ no natty)]
  | Nil <- tm  = pure []
  | Just (Sone, [t]) <- tagEh tm = checkEval ty t >>= \r -> pure [Right r]
  | Just (Splus, [s, t]) <- tagEh tm = (++) <$> termToNFList ty s <*> termToNFList ty t
  | otherwise = withScope $ error $ "termToNFList: no\nty = " ++ show ty ++ "\n m = " ++ show tm

termToNFAbel
  :: Typ ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFAbel n)
termToNFAbel ty tm
  | Just tm <- E $? tm = evalSynth tm >>= \(tm, ty') -> case E $? tm of
     _ | isUnitType ty' -> pure mempty
     Just _ -> pure $ NFAbel 0 [(tm, 1)]
     Nothing -> termToNFAbel ty tm
  | Intg i  <- tm  = pure $ NFAbel { nfConst = i, nfStuck = [] }
  | Nil <- tm  = pure mempty
  | Just (Sone, [t]) <- tagEh tm = checkEval ty t >>= \case
     Nil -> pure $ NFAbel 1 []
     t   -> withScope $ pure $ NFAbel 0 [(mk Sone t, 1)]
  | Just (Splus, [s, t]) <- tagEh tm = (<>) <$> termToNFAbel ty s <*> termToNFAbel ty t
  | Just [Intg i, t] <- tupEh tm =
      if i == 0 then pure mempty else fmap (i *) <$> termToNFAbel ty t
  | otherwise = error "termToNFAbel: no"

-- the input terms (s, t) better be of type [List One]
natTermCancel :: CancellerM (TC n) (Term Chk ^ n)
natTermCancel (s, t) = withScope $ do
  s <- termToNFAbel oneType s
  t <- termToNFAbel oneType t
  let (s', t') = cancelNFAbel cancelNat (s, t)
  pure (nfAbelToTerm s', nfAbelToTerm t')

termToNFBool :: Term Chk ^ n -> TC n (NFBool (Norm Syn ^ n))
termToNFBool tm
  | Just tm <- E $? tm = evalSynth tm >>= \(tm, _) -> case E $? tm of
     Just tm -> pure $ AND [tm]
     Nothing -> termToNFBool tm
  | Intg 0  <- tm = pure FALSE
  | Intg 1  <- tm = pure mempty
  | Just (Sand, [s, t]) <- tagEh tm = (<>) <$> termToNFBool s <*> termToNFBool t
  | otherwise = error "termToNFBool: no"

checkEvalMatrixNF
  :: (Eq h, Monoid h, Show h)
  => (Typ ^ n -> Term Chk ^ n -> TC n h)
  -> (NmTy ^ n, NmTy ^ n, NmTy ^ S (S n))  -- (rowTy, colTy, \row col. cellTy) -- NOT rowGenTy and colGenTy
  -> Corner n        -- (rs, cs)
  -> Term 'Chk ^ n
  -> TC n ( NFMatrix h (Norm Chk ^ n) (Norm Syn ^ n)
          , ( Corner n -- (rs1, cs0), down the left and below
            , Corner n -- (rs0, cs1), rightwards and along the top
          ) )          -- invariant : rs = rs0 + rs1, cs = cs0 + cs1
checkEvalMatrixNF nf ty@(rowTy, colTy, cellTy) mx@(rs, cs) tm
  | Just (Sone, [t]) <- tagEh tm = withScope $ do
    (r, rs') <- uncons rowTy rs
    (c, cs') <- uncons colTy cs
    let sig = subSnoc (sub0 (R $^ r <&> rowTy)) (R $^ c <&> colTy)
    v <- checkEval (cellTy //^ sig) t
    h <- nf rowTy $ mk Sone r
    pure ([[(h, [NFCell v])]] , ((rs', mk Sone c), (mk Sone r, cs')))
  | Just (Shjux, [l, r]) <- tagEh tm = withScope $ do
    (lm, ((rs', cs0), rt@(rs0, _))) <- checkEvalMatrixNF nf ty mx l
    (rm, ((_, cs1), (_, cs''))) <- checkEvalMatrixNF nf ty rt r
    pure (lm `hjux` rm,  ((rs', mk Splus cs0 cs1), (rs0, cs'')))
  | Just (Svjux, [t, b]) <- tagEh tm = withScope $ do
    (tm, (lb@(_, cs0), (rs0, cs'))) <- track ("checkEval VJUX " ++ show tm) $ checkEvalMatrixNF nf ty mx t
    (bm, ((rs'', _), (rs1, _))) <- checkEvalMatrixNF nf ty lb b
    pure (tm `vjux` bm, ((rs'', cs0), (mk Splus rs0 rs1, cs')))
  | Just (Splus, [x, y]) <- tagEh tm = withScope $ do
    (xm, corners) <- checkEvalMatrixNF nf ty mx x
    (ym, _) <- checkEvalMatrixNF nf ty mx y
    pure (xm `madd` ym, corners)
  | Just tm <- E $? tm = withScope $ do
    (tm, ty') <- evalSynthNmTy tm
    case E $? tm of
      Nothing -> checkEvalMatrixNF nf ty mx tm
      Just tm -> case tagEh ty' of
        Just (SMatrix, [_, _, _,  rs0, cs0]) -> do
          (rs0, rs1) <- prefixEh rowTy rs0 rs
          (cs0, cs1) <- prefixEh colTy cs0 cs
          h   <- nf rowTy rs0
          pure ([[(h, [NFNeutral tm])]], ((rs1, cs0), (rs0, cs1)))
        _ -> fail "checkEvalMatrixAbel"
  | otherwise = withScope $ fail $ "checkEvalMatrixNF: not a valid matrix ctor " ++ show tm


propEh :: Typ ^ n -> TC n Bool
propEh ty = isUnitType <$> typeEval ty

-- TODO : do more subtyping

-- subtyping is not coercive, it is subsumptive, i.e., any terms that
-- checks at the subtype must also check at the supertype
-- unadulterated
subtypeEh :: NmTy ^ n -> NmTy ^ n -> TC n ()
subtypeEh got want = withScope $
  case (tagEh got, tagEh want) of
    (Just (SEnum, [gs]), Just (SEnum, [ws])) -> do
      let tyA = atom SAtom
      ngs <- termToNFList tyA gs
      nws <- termToNFList tyA ws
      () <$ must "Subtype" (stripPrefix ngs nws)
    (Just (SPi, [gs, gt]), Just (SPi, [ws, wt]))
      | Just gt' <- lamEh gt, Just (x, wt') <- lamNameEh wt -> do
        subtypeEh ws gs
        under (x, ws) $ subtypeEh gt' wt'
    (Just (SSig, [gs, gt]), Just (SSig, [ws, wt]))
      | Just (x, gt') <- lamNameEh gt, Just wt' <- lamEh wt -> do
        subtypeEh gs ws
        under (x, gs) $ subtypeEh gt' wt'
    (Just (SAbel, [g]), Just (SAbel, [g'])) ->
      subtypeEh g g'
    (Just (SQuantity, [genTy, dim]), Just (SQuantity, [genTy', dim'])) -> do
      subtypeEh genTy genTy'
      guard $ dim == dim'
    _ -> guard $ got == want

etaExpand
  :: Term Chk ^ n  -- *evaluated* term, but not eta-long
  -> NmTy ^ n      -- \
  -> NmTy ^ n      --- allowed to assume these types pass subtype check
  -> TC n (Norm Chk ^ n)
etaExpand tm gotTy wantTy
  | Just tm <- E $? tm
  , Just gotTy <- tagEh gotTy
  , Just twantTy <- tagEh wantTy = withScope $
    case (gotTy, twantTy) of
      ((SPi, [gs, gt]), (SPi, [ws, wt]))
        | Just gt' <- lamEh gt, Just (name, wt') <- lamNameEh wt ->
            (lam name <$>) . under (name, ws) $ do
            arg <- etaExpand (evar 0) (wk ws) (wk gs)
            etaExpand (E $^ D $^ wk tm <&> arg) gt' wt'
      ((SSig, [gs, gt]), (SSig, [ws, wt]))
        | Just gt' <- lamEh gt, Just wt' <- lamEh wt -> do
           let tm0 = D $^ tm <&> atom Sfst
           a  <- etaExpand (E $^ tm0) gs ws
           let sig = sub0 tm0
           gt <- typeEval (gt' //^ sig)
           wt <- typeEval (wt' //^ sig)
           d  <- etaExpand (E $^ D $^ tm <&> atom Ssnd) gt wt
           pure (T $^ a <&> d)
      _ | isUnitType wantTy -> pure nil
      _  -> pure (E $^ tm)
  | otherwise = pure tm
