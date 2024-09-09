{- AUTOCOLLECT.TEST -}

module Test.CoreTT (
  {- AUTOCOLLECT.TEST.export -}
) where

import qualified Data.Map as Map

import CoreTT (TC, emptyStore, runTC, checkEh, checkEval, typeEh, evalSynth)
import qualified CoreTT as TT

import Term
import NormalForm
import MagicStrings

import Test.Tasty (TestTree)
import Test.Tasty.HUnit

infixr 5 ==>
(==>) :: Type ^ S Z -> Type ^ S Z -> Type ^ S Z
src ==> (tgt :^ th) = mk SPi src (K tgt :^ th)

testShowTC :: TC n (Term 'Chk ^ n)
           -> Context n
           -> String
testShowTC tc ctx =
  case runTC tc emptyStore ctx of
    Left err -> err
    Right tm -> tmShow False tm (rootNamespace, fst <$> ctx)


abel :: NATTY n => Type ^ n
abel = mk SAbel SOne

list :: NATTY n => Type ^ n
list = mk SList SOne

toA :: NATTY n => String -> Term Chk ^ n
toA s = mk Sone (atom s)

test = testCase "Eval Abel (prop): x + y" $ do
  let tm = evar 0 + evar 1
  let ctx = VN :# ("y", abel) :# ("x", abel)
  testShowTC (checkEval abel tm) ctx
    @?= "['plus y x]"

test = testCase "Eval Abel (prop): y + x" $ do
  let tm = evar 1 + evar 0
  let ctx = VN :# ("y", abel) :# ("x", abel)
  testShowTC (checkEval abel tm) ctx
    @?= "['plus y x]"

test = testCase "Eval Abel (prop): x + x" $ do
  let tm = evar 0 + evar 0
  let ctx = VN :# ("x", abel)
  testShowTC (checkEval abel tm) ctx
    @?= "[2 x]"

test = testCase "Eval Abel (prop): x + 3 + x" $ do
  let tm = evar 0 + 3 + evar 0
  let ctx = VN :# ("x", abel)
  testShowTC (checkEval abel tm) ctx
    @?= "['plus 3 [2 x]]"

test = testCase "Eval Abel (prop): (int 5) :: Abel One" $ do
  let tm = mk Sone $ lit (5 :: Int)
  testShowTC (checkEval abel tm) emptyContext
    @?= "1"

test = testCase "Eval List (prop): x + y" $ do
  let tm = evar 0 + evar 1
  let ctx = VN :# ("y", list) :# ("x", list)
  testShowTC (checkEval list tm) ctx
    @?= "['plus y x]"

test = testCase "Eval List (non-prop): x + y" $ do
  let ty = mk SList SType
  let tm = evar 0 + evar 1
  let ctx =  VN :# ("y", ty) :# ("x", ty)
  testShowTC (TT.checkEval ty tm) ctx
    @?= "['plus x y]"

test = testCase "Eval List (prop): y + x" $ do
  let tm = evar 1 + evar 0
  let ctx = VN :# ("y", list) :# ("x", list)
  testShowTC (checkEval list tm) ctx
    @?= "['plus y x]"

test = testCase "Eval List (prop): x + 3 + x" $ do
  let tm = evar 0 + 3 + evar 0
  let ctx = VN :# ("x", list)
  testShowTC (checkEval list tm) ctx
    @?= "['plus 3 [2 x]]"

test = testCase "Chk List (prop): x + 3 + x" $ do
  let tm = (evar 0 + 3) + evar 0
  let ctx = VN :# ("x", list)
  runTC (checkEh list tm) emptyStore ctx
    @?= Right ()

test = testCase "Chk List (prop): x - 3 + x" $ do
  let tm = evar 0 + (-3) + evar 0
  let ctx = VN :# ("x", list)
  runTC (checkEh list tm) emptyStore ctx
    @?= Left "checkCanEh: negative length list"

test = testCase "Chk 'a :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = atom "a"
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk 'd :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = atom "d"
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Left "checkEnumEh: position of atom 'd not determined."

test = testCase "Chk 2 :: Enum('a, 'b, 'c):" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = lit (2 :: Int)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk 5 :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = lit (5 :: Int)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Left "checkEnumEh: tag at index not determined."

test = testCase "Chk 'b + 1 :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = atom "b" + 1
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Eval 'b + 1 :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = atom "b" + 1
  testShowTC (checkEval ty tm) emptyContext
    @?= "2"

test = testCase "Chk 'b + 2 :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = atom "b" + 2
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Left "checkEnumEh: tag at index not determined."

test = testCase "Chk (x :: atom) :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = evar 0
  let ctx = VN :# ("x", atom SAtom)
  runTC (checkEh ty tm) emptyStore ctx
    @?= Left "TC monad"

test = testCase "Chk (x :: Enum('a, 'b, 'c)) :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let ty = mk SEnum atoms
  let tm = evar 0
  let ctx = VN :# ("x", ty)
  runTC (checkEh ty tm) emptyStore ctx
    @?= Right ()

test = testCase  "Chk (x :: Enum('a, 'b)) :: Enum('a, 'b, 'c)" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let subatoms = toA "a" + toA "b"
  let ty = mk SEnum atoms
  let subty = mk SEnum subatoms
  let tm = evar 0
  let ctx = VN :# ("x", subty)
  runTC (checkEh ty tm) emptyStore ctx
    @?= Right ()

test = testCase "Chk (y :: Enum(z)) :: Enum(z + ('a, 'b', c'))" $ do
  let atoms = toA "a" + toA "b" + toA "c"
  let zty = mk SList SAtom
  let yty = mk SEnum (evar 2)
  let xty = mk SEnum atoms
  let ty  = mk SEnum (evar 2 + atoms)
  let tm = evar 1
  let ctx = VN :# ("z", zty) :# ("y", yty) :# ("x", xty)
  runTC (checkEh ty tm) emptyStore ctx
    @?= Right ()

test = testCase "Type Pi: (X : Type) -> (x : X) -> x" $ do
  let body = mk SPi (evar 0) (lam "x" (evar 1))
  let ty = mk SPi SType (lam "X" body)
  runTC (typeEh ty) emptyStore emptyContext
    @?= Right ()

test = testCase "Eval Pi: f :: (X : Type) -> X" $ do
  let ty = mk SPi SType (lam "X" $ atom SType)
  let tm = evar 0
  let ctx = VN :# ("f", ty)
  testShowTC (checkEval ty tm) ctx
    @?= "(\\_. f(_))"

test = testCase "Chk Pi: \\X x. x :: (X : Type) -> (x : X) -> X" $ do
  let body = mk SPi (evar 0) (lam "x" (evar 1))
  let ty = mk SPi SType (lam "X" body)
  let tm = lam "X" $ lam "x" (evar 0)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase  "Chk Pi: \\X f x. f (f x) :: (X : Type) -> (f : X -> X) -> X -> X" $ do
  let body = (evar 0 ==> evar 0) ==> evar 0 ==> evar 0
  let ty = mk SPi SType (lam "X" body)
  let tm = lam "X" $ lam "f" $ lam "x" $
             E $^ D $^ var 1 <&> (E $^ D $^ var 1 <&> evar 0)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk Pi: \\X f x : f (x x) :: (X : Type) -> (f : X -> X) -> X -> X" $ do
  let body = (evar 0 ==> evar 0) ==> evar 0 ==> evar 0
  let ty = mk SPi SType (lam "X" body)
  let tm = lam "X" $ lam "f" $ lam "x" $
             E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Left "synthEh: no"

test = testCase "Eval Sig: x :: Sigma Type \\X . x" $ do
  let ty = mk SSig SType (lam "X" $ atom SType)
  let tm = evar 0
  let ctx = VN :# ("x", ty)
  testShowTC (checkEval ty tm) ctx
    @?= "[x('fst) | x('snd)]"

test = testCase "EvalSyn Sig: snd (One, x) :: Sigma Type \\X . X" $ do
  let ty = mk SSig SType (lam "X" (evar 0))
  let tm = D $^ (R $^ (T $^ atom SOne <&> evar 0) <&> ty) <&> atom Ssnd
  let ctx = VN :# ("x", atom SOne)
  testShowTC (fst <$> evalSynth tm) ctx
    @?= "[]"

test = testCase "EvalSyn Sig: snd (One, z) :: Sigma Type \\X . X" $ do
  let ty = mk SSig SType (lam "X" (evar 0))
  let tm = D $^ (R $^ (T $^ atom SOne <&> evar 2) <&> ty) <&> atom Ssnd
  let ctx = VN :# ("x", atom SOne) :# ("y", atom SOne) :# ("z", atom SOne)
  testShowTC (fst <$> evalSynth tm) ctx
    @?= "[]"

test = testCase "Eval x :: Sigma ((X:Type) -> X) \\_ . Type" $ do
  let aty = mk SPi SType (lam "X" $ atom SType) :: Type ^ S Z
  let ty = mk SSig aty (lam "X" $ atom SType)
  let ctx = VN :# ("x", ty)
  let tm = evar 0
  testShowTC (checkEval ty tm) ctx
    @?= "[(\\_. x('fst)(_)) | x('snd)]"

test = testCase "Chk 99 :: Char" $ do
  let ty = atom SChar
  let tm = lit (99 :: Int)
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk [()] :: Matrix [()] [()] \\_ _ . Type" $ do
  let rs = mk Sone nil :: Term Chk ^ Z
  let cs = mk Sone nil :: Term Chk ^ Z
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let tm = mk Sone SOne
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk [()] +h+ [()] :: Matrix [()] [(), ()] \\_ _ . Type" $ do
  let rs = mk Sone nil :: Term Chk ^ Z
  let cs' = mk Sone nil :: Term Chk ^ Z
  let cs = cs' + cs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let tm' = mk Sone SOne :: Term Chk ^ Z
  let tm = mk Shjux tm' tm' :: Term Chk ^ Z
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()


test = testCase "Chk [()] +v+ [()] :: Matrix [(), ()] [()] \\_ _ . Type" $ do
  let rs' = mk Sone nil :: Term Chk ^ Z
  let cs = mk Sone nil :: Term Chk ^ Z
  let rs = rs' + rs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let tm' = mk Sone SOne :: Term Chk ^ Z
  let tm = mk Svjux tm' tm' :: Term Chk ^ Z
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test = testCase "Chk ([()] +h+ [()]) +v+ ([()] +h+ [()]) :: Matrix [(), ()] [(), ()] \\_ _ . Type" $ do
  let rs' = mk Sone nil :: Term Chk ^ Z
  let cs' = mk Sone nil :: Term Chk ^ Z
  let cs = cs' + cs'
  let rs = rs' + rs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let cell = mk Sone SOne :: Term Chk ^ Z
  let row = mk Shjux cell cell :: Term Chk ^ Z
  let tm  = mk Svjux row row :: Term Chk ^ Z
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Right ()

test =  testCase "Chk ([()] +h+ [()]) +v+ ([()] +h+ [()]) :: Matrix [(), ()] [(), ()] \\_ _ . Foo" $ do
  let rs' = mk Sone nil :: Term Chk ^ Z
  let cs' = mk Sone nil :: Term Chk ^ Z
  let cs = cs' + cs'
  let rs = rs' + rs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let cell = mk Sone ("Foo" :: String) :: Term Chk ^ Z
  let row = mk Shjux cell cell :: Term Chk ^ Z
  let tm  = mk Svjux row row :: Term Chk ^ Z
  runTC (checkEh ty tm) emptyStore emptyContext
    @?= Left "typeEh: unknown type Foo"


test = testCase "Chk [()] +h+ [()] :: Matrix [(), ()] [(), ()] \\_ _ . Type" $ do
  let rs' = mk Sone nil :: Term Chk ^ Z
  let cs' = mk Sone nil :: Term Chk ^ Z
  let cs = cs' + cs'
  let rs = rs' + rs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let cell = mk Sone SOne :: Term Chk ^ Z
  let row = mk Shjux cell cell :: Term Chk ^ Z
  runTC (checkEh ty row) emptyStore emptyContext
    @?= Left "unnil: non-zero number"


type Term4 = Term Chk ^ S (S (S (S Z)))

test = testCase "Chk (x +h+ y) +v+ (x +h+ y) :: Matrix [(), ()] (i + j) \\_ _ . Type" $ do
  let i = evar 3 :: Term4
  let j = evar 1 :: Term4
  let mty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) :: Term4 -> Term4 -> Term4
  let one = mk Sone nil :: Term4
  let two = one + one
  let xty = mty one i
  let yty = mty one j
  let nat = mk SList SOne :: Term4
  let x = evar 2 :: Term4
  let y = evar 0 :: Term4
  let ctx = VN :# ("", nat) :# ("", xty) :# ("", nat) :# ("", yty)
  let tm = mk Svjux (mk Shjux x y :: Term4) (mk Shjux y x :: Term4) :: Term4
  let ty = mty two (i + j)
  runTC (checkEh ty tm) emptyStore ctx
    @?= Right ()

test = testCase "Chk ([()] +v+ [()]) +h+ ([()] +v+ [()]) :: Matrix [(), ()] (i + j) \\_ _ . Type" $ do
  let rs' = mk Sone nil :: Term Chk ^ Z
  let cs' = mk Sone nil :: Term Chk ^ Z
  let cs = cs' + cs'
  let rs = rs' + rs'
  let ty = mk SMatrix SOne SOne (lam "_" $ lam "_" $ atom SType) rs cs :: Term Chk ^ Z
  let cell = mk Sone SOne :: Term Chk ^ Z
  let col = mk Svjux cell cell :: Term Chk ^ Z
  let tm  = mk Shjux col col :: Term Chk ^ Z
  testShowTC (checkEval ty tm) emptyContext
    @?= "['vjux ['hjux ['one 'One] ['one 'One]] ['hjux ['one 'One] ['one 'One]]]"
