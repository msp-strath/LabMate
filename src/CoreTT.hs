module CoreTT where

import Control.Applicative
import Control.Monad
import Data.List (stripPrefix)
import NormalForm
import Term

-- types
pattern SType = "Type"
pattern SOne  = "One"
pattern SAbel = "Abel"
pattern SList = "List"
pattern SAtom = "Atom"
pattern SEnum = "Enum"
pattern SPi   = "Pi"
pattern SSig  = "Sigma"
pattern SMatrix = "Matrix"

-- eliminators
pattern Sfst  = "fst"
pattern Ssnd  = "snd"

pattern Shjux = "hjux"
pattern Svjux = "vjux"

newtype TC n x =
 TC { runTC :: (Natty n, Vec n (Type ^ n)) -> Either String x }

instance Functor (TC n) where
  fmap k (TC f) = TC $ fmap (fmap k) f

instance Applicative (TC n) where
  pure = return
  (<*>) = ap

instance Alternative (TC n) where
  empty = fail ""
  TC f <|> TC g = TC $ \ ga -> case f ga of
    Left msg -> case g ga of
      Left msg' -> Left $ msg ++ msg'
      r -> r
    r -> r

instance Monad (TC n) where
  return = TC . pure . pure
  (TC f) >>= k = TC $ \ga ->
    f ga >>= ($ ga) . runTC . k

instance MonadFail (TC n) where
  fail  = TC . const . Left

must :: MonadFail m => Maybe a -> m a
must (Just a) = pure a
must Nothing = fail ""

typeOf :: (S Z <= n) -> TC n (Type ^ n)
typeOf i = TC $ Right . vonly . (i ?^) . snd

scope :: TC n (Natty n)
scope = TC $ Right . fst

withScope :: (NATTY n => TC n t) -> TC n t
withScope c = do
  n <- scope
  nattily n c

under
  :: Type ^ n
  -> TC (S n) a
  -> TC n a -- discharging the bound variable is the caller's problem
under ty (TC f) = TC $ \(n, ctx) -> f (Sy n, wk <$> (ctx :# ty))

typeEh :: Term Chk ^ n -> TC n ()
typeEh ty | Just cts <- tagEh ty = case cts of
  (SOne, [])   -> pure ()
  (SAtom, [])  -> pure ()
  (SType, [])  -> pure ()
  (SAbel, [t]) -> typeEh t
  (SList, [t]) -> typeEh t
  (SEnum, [t]) -> withScope $
    checkEh (mk SList $ atom SAtom) t
  (SPi, [s, t]) | Just t' <- lamEh t -> do
    typeEh s
    under s $ typeEh t'
  (SSig, [s, t]) | Just t' <- lamEh t -> do
    typeEh s
    under s $ typeEh t'
  (SMatrix, [rowTy, colTy, cellTy, rs, cs])
    | Just cellTy <- lamEh cellTy
    , Just cellTy <- lamEh cellTy -> withScope $ do
      typeEh rowTy
      typeEh colTy
      under rowTy $ under (wk colTy) $ typeEh cellTy
      checkEh (mk SList rowTy) rs
      checkEh (mk SList colTy) cs
  (ty, _) -> fail $ "typeEh: unknown type " ++ ty
typeEh ty | Just ty <- E $? ty = withScope $ do
  gotTy <- synthEh ty
  subtypeEh gotTy $ atom SType
typeEh _ = fail "typeEh: not a type"

checkEh
  :: Type ^ n {- Ty -}
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
  (SOne, []) -> pure True
  (SAtom, []) | Atom _ <- tm -> pure True
  (SPi, [s, t]) | Just t' <- lamEh t, Just tm' <- lamEh tm ->
    True <$ under s (checkEh t' tm')
  (SSig, [s, t]) | Just t' <- lamEh t, Just (a, d) <- pairEh tm -> withScope $ do
    checkEh s a
    True <$ checkEh (t' //^ sub0 (R $^ a <&> s)) d
  (SType, []) -> True <$ typeEh tm
  (SMatrix, [rowTy, colTy, cellTy, rs, cs])
    | Just cellTy <- lamEh cellTy
    , Just cellTy <- lamEh cellTy -> do
      ((rs', _), (_, cs')) <- checkCanMatrixEh (rowTy, colTy, cellTy) (rs, cs) tm
      True <$ unnil rowTy rs' <* unnil colTy cs'
  _ -> pure False
checkCanEh _ _ = pure False

type Corner n = ( Term 'Chk ^ n -- rowHeaders vertically on the left
                , Term 'Chk ^ n -- columnHeaders horizontaly on the top
                )

checkCanMatrixEh
  :: (NmTy ^ n, NmTy ^ n, NmTy ^ S (S n))  -- \row col. cellTy
  -> Corner n        -- (rs, cs)
  -> Term 'Chk ^ n
  -> TC n ( Corner n -- (rs1, cs0), down the left and below
          , Corner n -- (rs0, cs1), rightwards and along the top
          )          -- invariant : rs = rs0 + rs1, cs = cs0 + cs1
checkCanMatrixEh ty@(rowTy, colTy, cellTy) (rs, cs) tm
  | Just (Sone, [t]) <- tagEh tm = withScope $ do
    (r, rs') <- uncons rowTy rs
    (c, cs') <- uncons colTy cs
    let sig = subSnoc (sub0 (R $^ r <&> rowTy)) (R $^ c <&> colTy)
    checkEh (cellTy //^ sig) t
    pure ((rs', mk Sone c), (mk Sone r, cs'))
  | Just (Shjux, [l, r]) <- tagEh tm = withScope $ do
    ((rs', cs0), (rs0, cs')) <- checkCanMatrixEh ty (rs, cs) l
    ((rs'', cs1), (_, cs'')) <- checkCanMatrixEh ty (rs0, cs') r
    unnil rowTy rs''
    pure ((rs', mk Splus cs0 cs1), (rs0, cs''))
  | Just (Svjux, [t, b]) <- tagEh tm = withScope $ do
    ((rs', cs0), (rs0, cs')) <- checkCanMatrixEh ty (rs, cs) t
    ((rs'', _), (rs1, cs'')) <- checkCanMatrixEh ty (rs', cs0) b
    unnil colTy cs''
    pure ((rs'', cs0), (mk Splus rs0 rs1, cs''))
  | otherwise = undefined

uncons :: Type ^ n -> Term Chk ^ n -> TC n (Term Chk ^ n, Term Chk ^ n)
uncons elty xs = withScope $ propEh elty >>= \case
  True  -> termToNFAbel elty xs >>= \case
    t@NFAbel{..} -> do
      guard (nfConst > 0)
      pure  (nil, nfAbelToTerm (t {nfConst = nfConst - 1}))
  False -> termToNFList elty xs >>= \case
    (Right t) : ts -> pure (t, nfListToTerm ts)
    (Left _) : _ -> fail "uncons: stuck head"
    _ -> fail "uncons: empty list"

unnil :: Type ^ n -> Term Chk ^ n -> TC n ()
unnil elty xs = withScope $ propEh elty >>= \case
  True  -> termToNFAbel elty xs >>= \case
    NFAbel{nfConst = 0, nfStuck = []} -> pure  ()
    _ -> fail "unnil : non-zero number"
  False -> termToNFList elty xs >>= \case
    [] -> pure ()
    _ -> fail "unnil: non-empty list"


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
  _ -> fail "checkEnumEh: "

synthEh
  :: Term Syn ^ n    {- t -}
  -> TC n (Type ^ n) {- t \in T, T need *not* be normal -}
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

checkNormEval
  :: NmTy ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Norm Chk ^ n)
checkNormEval wantTy tm | Just tm <- E $? tm = do
  (tm, gotTy) <- evalSynth tm
  transport tm gotTy wantTy
checkNormEval ty tm | Just ty <- tagEh ty = withScope $ case ty of
  (SType, []) -> typeEval tm
  (SOne, []) -> pure nil
  (SAtom, []) -> pure tm
  (SAbel, [genTy]) -> nfAbelToTerm <$> termToNFAbel genTy tm
  (SList, [genTy]) -> propEh genTy >>= \case
      True  -> nfAbelToTerm <$> termToNFAbel genTy tm
      False -> nfListToTerm <$> termToNFList genTy tm
  (SEnum, [as]) -> termToNFList (atom SAtom) as >>= \x ->
      pure $ case findInEnum tm x of
        Just (i, _)  -> int i
        -- TODO : handle neutrals, reduce further
        _ -> tm
  (SPi, [s, t])
    | Just t' <- lamEh t
    , Just (x, tm') <- lamNameEh tm ->
        lam x <$> under s (checkNormEval t' tm')
  (SSig, [s, t])
    | Just  t' <- lamEh t
    , Just (a, d) <- pairEh tm -> do
        a <- checkNormEval s a
        d <- checkEval (t' //^ sub0 (R $^ a <&> s)) d
        pure (T $^ a <&> d)
  (t, _) -> fail $ "checkNormEval: unknown type " ++ t
checkNormEval _ _ = fail "checkNormEval: no"

checkEval
  :: Type ^ n {- Ty -}
  -> Term Chk ^ n {- tm -}
  -- must be Ty \ni tm, i.e. already checked
  -> TC n (Norm Chk ^ n)
checkEval ty tm = do
  ty <- typeEval ty
  checkNormEval ty tm

typeEval :: Type ^ n -> TC n (NmTy ^ n)
typeEval ty | Just ty <- tagEh ty = withScope $ case ty of
  (x, []) | x `elem` [SAtom, SOne, SType] -> pure $ atom x
  (SAbel, [genTy]) -> mk SAbel <$> typeEval genTy
  (SList, [genTy]) -> mk SList <$> typeEval genTy
  (SEnum, [as]) -> mk SEnum <$> checkNormEval (mk SList (atom SAtom)) as
  (SPi, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SPi <$> typeEval s <*> (lam x <$> under s (typeEval t'))
  (SSig, [s, t]) | Just (x, t') <- lamNameEh t ->
      mk SSig <$> typeEval s <*> (lam x <$> under s (typeEval t'))
  (SMatrix, [rowTy, colTy, cellTy, rs, cs])
    | Just (r, cellTy) <- lamNameEh cellTy, Just (c,cellTy) <- lamNameEh cellTy -> do
      mk SMatrix <$> typeEval rowTy
                 <*> typeEval colTy
                 <*> (lam r <$> under rowTy (lam c <$> under (wk colTy) (typeEval cellTy)))
                 <*> checkEval (mk SList rowTy) rs
                 <*> checkEval (mk SList colTy) cs
  (ty, _) -> fail $ "typeEval: unknown type " ++ ty
typeEval ty | Just ty <- E $? ty = fst <$> evalSynth ty
typeEval ty = fail "typeEval: no"

-- there is no guarantee that the returned term is the canonical
-- representative of its eq. class because it is *not* eta-long.
evalSynth :: Term Syn ^ n -> TC n (Term Chk ^ n, Type ^ n)
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
      _ -> fail "evalSynth: eliminator for an unknown type"
  _ -> fail "evalSynthEh: no"

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

termToNFList
  :: Type ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFList n)
termToNFList ty tm
  | Just tm <- E $? tm = evalSynth tm >>= \(tm, _) -> case E $? tm of
      Just tm -> pure [Left tm]
      Nothing -> termToNFList ty tm
  | Intg i <- tm = withScope $ pure $ replicate (fromInteger i) (Right nil)
  | Nil <- tm  = pure []
  | Just (Sone, [t]) <- tagEh tm = checkEval ty t >>= \r -> pure [Right r]
  | Just (Splus, [s, t]) <- tagEh tm = (++) <$> termToNFList ty s <*> termToNFList ty t
  | otherwise = error "termToNFList: no"

termToNFAbel
  :: Type ^ n     -- type of generators
  -> Term Chk ^ n
  -> TC n (NFAbel n)
termToNFAbel ty tm
  | Just tm <- E $? tm = evalSynth tm >>= \(tm, _) -> case E $? tm of
     Just _ -> pure $ NFAbel 0 [(tm, 1)]
     Nothing -> termToNFAbel ty tm
  | Intg i  <- tm  = pure $ NFAbel { nfConst = i, nfStuck = [] }
  | Nil <- tm  = pure mempty
  | Just (Sone, [t]) <- tagEh tm = checkEval ty t >>= \case
     Nil -> pure $ NFAbel 1 []
     _   -> withScope $ pure $ NFAbel 0 [(mk Sone t, 1)]
  | Just (Splus, [s, t]) <- tagEh tm = (<>) <$> termToNFAbel ty s <*> termToNFAbel ty t
  | Just [Intg i, t] <- tupEh tm =
      if i == 0 then pure mempty else fmap (i *) <$> termToNFAbel ty t
  | otherwise = error "termToNFAbel: no"

propEh :: Type ^ n -> TC n Bool
propEh ty = do
  n <- scope
  typeEval ty >>= \case
    Atom SOne -> pure True
    _         -> pure False

-- TODO : do more subtyping
subtypeEh :: NmTy ^ n -> NmTy ^ n -> TC n ()
subtypeEh got want = withScope $
  case (tagEh got, tagEh want) of
    (Just (SEnum, [gs]), Just (SEnum, [ws])) -> do
      let tyA = atom SAtom
      ngs <- termToNFList tyA gs
      nws <- termToNFList tyA ws
      () <$ must (stripPrefix ngs nws)
    (Just (SPi, [gs, gt]), Just (SPi, [ws, wt]))
      | Just gt' <- lamEh gt, Just wt' <- lamEh wt -> do
        subtypeEh ws gs
        under ws $ subtypeEh gt' wt'
    (Just (SSig, [gs, gt]), Just (SSig, [ws, wt]))
      | Just gt' <- lamEh gt, Just wt' <- lamEh wt -> do
        subtypeEh gs ws
        under gs $ subtypeEh gt' wt'
    (_, Just (SOne, [])) -> pure ()
    _ -> guard $ got == want

transport
  :: Term Chk ^ n  -- *evaluated* term, but not eta-long
  -> NmTy ^ n      -- \
  -> NmTy ^ n      -- allowed to assume these types pass subtype check
  -> TC n (Norm Chk ^ n)
transport tm gotTy wantTy
  | Just tm <- E $? tm
  , Just gotTy <- tagEh gotTy
  , Just wantTy <- tagEh wantTy =
    case (gotTy, wantTy) of
      ((SPi, [gs, gt]), (SPi, [ws, wt]))
        | Just gt' <- lamEh gt, Just (name, wt') <- lamNameEh wt ->
          withScope $ (lam name <$>) . under ws $ do
            arg <- transport (evar 0) (wk ws) (wk gs)
            transport (E $^ D $^ wk tm <&> arg) gt' wt'
      ((SSig, [gs, gt]), (SSig, [ws, wt]))
        | Just gt' <- lamEh gt, Just wt' <- lamEh wt -> withScope $ do
           let tm0 = D $^ tm <&> atom Sfst
           a  <- transport (E $^ tm0) gs ws
           let sig = sub0 tm0
           gt <- typeEval (gt' //^ sig)
           wt <- typeEval (wt' //^ sig)
           d  <- transport (E $^ D $^ tm <&> atom Ssnd) gt wt
           pure (T $^ a <&> d)
      _  -> pure (E $^ tm)
  | otherwise = pure tm

------------ testing -----------------------

(==>) :: Type ^ S Z -> Type ^ S Z -> Type ^ S Z
src ==> (tgt :^ th) = mk SPi src (K tgt :^ th)

testShowTC :: TC n (Term 'Chk ^ n)
           -> Vec n (Name, Type ^ n)
           -> String
testShowTC tc ctx =
  case runTC tc (vlen ctx, snd <$> ctx) of
    Left err -> err
    Right tm -> tmShow False tm (fst <$> ctx)

{-
test1 = let ty = mk SPi SType (lam "X" body)
            body = mk SPi (var 0) (lam "x" (E $^ var 1))
         in runTC (typeEh ty) (natty, VN)

test2 = let ty = mk SPi SType (lam "X" body)
            body = mk SPi ( var 0) (lam "x" (E $^ var 1))
            tm = lam "X" $ lam "x" (E $^ var 0)
         in runTC (checkEh ty tm) (natty, VN)

test3 = let ty = mk SPi SType (lam "X" body)
            body = (evar 0 ==> evar 0) ==> (evar 0 ==> evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 1 <&> evar 0)
        in runTC (checkEh ty tm) (natty, VN)

test4 = let ty = mk SPi SType (lam "X" body)
            body = (evar 0 ==> evar 0) ==> (evar 0 ==> evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
         in runTC (checkEh ty tm) (natty, VN)
         -- Left "synthEh: no"

test5 = let ty = mk SPi SType (lam "X" body)
            body = (evar 0 ==> evar 0) ==> (evar 0 ==> evar 0)
            tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
        in runTC (checkEh ty tm) (natty, VN)
         -- Left "synthEh : no"
-}

test6 = let ty = mk SSig SType (lam "X" (evar 0))
            -- tm = snd (SOne, var 2)
            tm = D $^ (R $^ (T $^ atom SOne <&> evar 2) <&> ty) <&> atom Ssnd
            ctx = VN :# ("x", atom SOne) :# ("y", atom SOne) :# ("z", atom SOne)
        in  testShowTC (fst <$> evalSynth tm) ctx

test7 = let ty = mk SPi SType (lam "X" $ atom SType)
            ctx = VN :# ("f", ty)
            tm = evar 0
        in testShowTC (checkEval ty tm) ctx

test8 = let ty = mk SSig SType (lam "X" $ atom SType)
            ctx = VN :# ("x", ty)
            tm = evar 0
        in testShowTC (checkEval ty tm) ctx

test9 = let aty = mk SPi SType (lam "X" $ atom SType) :: Type ^ S Z
            ty = mk SSig aty (lam "X" $ atom SType)
            ctx = VN :# ("x", ty)
            tm = evar 0
        in testShowTC (checkEval ty tm) ctx

test10 = let rs = mk Sone nil :: Term Chk ^ Z
             cs = mk Sone nil :: Term Chk ^ Z
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             tm = mk Sone SOne
         in runTC (checkEh ty tm) (natty, VN)

test11 = let rs = mk Sone nil :: Term Chk ^ Z
             cs' = mk Sone nil :: Term Chk ^ Z
             cs = cs' + cs'
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             tm' = mk Sone SOne :: Term Chk ^ Z
             tm = mk Shjux tm' tm' :: Term Chk ^ Z
         in runTC (checkEh ty tm) (natty, VN)

test12 = let rs' = mk Sone nil :: Term Chk ^ Z
             cs = mk Sone nil :: Term Chk ^ Z
             rs = rs' + rs'
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             tm' = mk Sone SOne :: Term Chk ^ Z
             tm = mk Svjux tm' tm' :: Term Chk ^ Z
         in runTC (checkEh ty tm) (natty, VN)

test13 = let rs' = mk Sone nil :: Term Chk ^ Z
             cs' = mk Sone nil :: Term Chk ^ Z
             cs = cs' + cs'
             rs = rs' + rs'
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             cell = mk Sone SOne :: Term Chk ^ Z
             row = mk Shjux cell cell :: Term Chk ^ Z
             tm  = mk Svjux row row :: Term Chk ^ Z
         in runTC (checkEh ty tm) (natty, VN)

test14 = let rs' = mk Sone nil :: Term Chk ^ Z
             cs' = mk Sone nil :: Term Chk ^ Z
             cs = cs' + cs'
             rs = rs' + rs'
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             cell = mk Sone "Foo" :: Term Chk ^ Z
             row = mk Shjux cell cell :: Term Chk ^ Z
             tm  = mk Svjux row row :: Term Chk ^ Z
         in runTC (checkEh ty tm) (natty, VN)

test15 = let rs' = mk Sone nil :: Term Chk ^ Z
             cs' = mk Sone nil :: Term Chk ^ Z
             cs = cs' + cs'
             rs = rs' + rs'
             ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
             cell = mk Sone SOne :: Term Chk ^ Z
             row = mk Shjux cell cell :: Term Chk ^ Z
             tm  = mk Svjux row row :: Term Chk ^ Z
         in runTC (checkEh ty row) (natty, VN)
