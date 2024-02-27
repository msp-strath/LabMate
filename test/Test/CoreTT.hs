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

test = testCase "Type Pi: \\(X : Type) (x : X) . x" $ do
  let body = mk SPi (evar 0) (lam "x" (evar 1))
  let ty = mk SPi SType (lam "X" body)
  runTC (typeEh ty) emptyStore emptyContext
    @?= Right ()

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

test = testCase "EvalSyn Sig: (One, x) :: (Sigma (X:Type), X)" $ do
  let ty = mk SSig SType (lam "X" (evar 0))
  let tm = D $^ (R $^ (T $^ atom SOne <&> evar 0) <&> ty) <&> atom Ssnd
  let ctx = VN :# ("x", atom SOne)
  testShowTC (fst <$> evalSynth tm) ctx
    @?= "[]"
