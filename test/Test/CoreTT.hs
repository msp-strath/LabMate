module Test.CoreTT where

import qualified Data.Map as Map

import CoreTT (testShowTC, checkEh, checkEval, typeEh, evalSynth, (==>))
import qualified CoreTT as TT
import Term hiding (testShow)
import Term.Natty
import Term.Vec
import NormalForm
import MagicStrings

import Test.Tasty(TestTree)
import Test.Tasty.HUnit

mkTest :: (Eq a, Show a, HasCallStack) => (String, a, a) -> TestTree
mkTest (name, val, exp) = testCase name $ val @?= exp

coreTests :: [TestTree]
coreTests = [ test0,  test1, test2, test3, test4, test5, test5', test6, test7
            , test8, test9, test10, test11, test12, test13, test14, test14'
            , test15, test16, test17, test18, test19, test20, test21, test22
            , test23, test24
            ]

runTC tc = TT.runTC tc Map.empty

test0 = mkTest
  ( "Eval Abel (prop): x + y"
  , let ty = mk SAbel SOne
        tm = evar 0 + evar 1
    in TT.testShowTC (checkEval ty tm) (VN :# ("y", ty) :# ("x", ty))
  , "['plus y x]"
  )

test1 = mkTest
  ( "Eval Abel (prop): y + x"
  , let ty = mk SAbel SOne
        tm = evar 0 + evar 1
    in testShowTC (checkEval ty tm) (VN :# ("y", ty) :# ("x", ty))
  , "['plus y x]"
  )

test2 = mkTest
  ( "Eval Abel (prop): x + x"
  , let ty = mk SAbel SOne
        tm = evar 0 + evar 0
    in testShowTC (checkEval ty tm) (VN :# ("x", ty))
  , "[2 x]"
  )

test3 = mkTest
  ( "Eval Abel (prop): x + 3 + x"
  , let ty = mk SAbel SOne
        tm = (evar 0 + 3) + evar 0
    in testShowTC (checkEval ty tm) (VN :# ("x", ty))
  , "['plus 3 [2 x]]"
  )

test4 = mkTest
  ( "Eval Abel (prop): (int 5) :: Abel One"
  , let ty = mk SAbel SOne
        tm = mk Sone $ lit (5 :: Int)
    in testShowTC (checkEval ty tm) VN
  , "1"
  )

test5 = mkTest
  ( "Eval List (prop): x + y"
  , let ty = mk SList SOne
        tm = evar 0 + evar 1
    in testShowTC (checkEval ty tm) (VN :# ("y", ty) :# ("x", ty))
  , "['plus y x]"
  )

test5' = mkTest
  ( "Eval List (non-prop): x + y"
  , let ty = mk SList SType
        tm = evar 0 + evar 1
    in testShowTC (TT.checkEval ty tm) (VN :# ("y", ty) :# ("x", ty))
  , "['plus x y]"
  )

test6 = mkTest
  ( "Eval List (prop): y + x"
  , let ty = mk SList SOne
        tm = evar 1 + evar 0
    in testShowTC (checkEval ty tm) (VN :# ("y", ty) :# ("x", ty))
  , "['plus y x]"
  )

test7 = mkTest
  ( "Eval List (prop): x + 3 + x"
  , let ty = mk SList SOne
        tm = (evar 0 + 3) + evar 0
    in testShowTC (TT.checkEval ty tm) (VN :# ("x", ty))
  , "['plus 3 [2 x]]"
  )

test8 = mkTest
  ( "Chk List (prop): x + 3 + x"
  , let ty = mk SList SOne
        tm = (evar 0 + 3) + evar 0
    in runTC (TT.checkEh ty tm) (natty, VN :# ty)
  , Right ()
  )

test9 = mkTest
  ( "Chk List (prop): x - 3 + x"
  , let ty = mk SList SOne
        tm = evar 0 + (-3) + evar 0
    in runTC (checkEh ty tm) (natty, VN :# ty)
  , Left "checkCanEh: negative length list"
  )

test10 = mkTest
  ( "Chk Enum('a, 'b, 'c): 'a"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = atom "a"
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Right ()
  )

test11 = mkTest
  ( "Chk Enum('a, 'b, 'c): 'd"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = atom "d"
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Left "checkEnumEh: position of atom 'd not determined."
  )

test12 = mkTest
  ( "Chk Enum('a, 'b, 'c): 2"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = lit (2 :: Int)
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Right ()
  )

test13 = mkTest
  ( "Chk Enum('a, 'b, 'c): 5"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = lit (5 :: Int)
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Left "checkEnumEh: tag at index not determined."
  )

test14 = mkTest
  ( "Chk Enum('a, 'b, 'c): 'b + 1"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = atom "b" + 1
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Right ()
  )

test14' = mkTest
  ( "Eval Enum('a, 'b, 'c): 'b + 1"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = atom "b" + 1
        f s = mk Sone (atom s)
   in testShowTC (checkEval ty tm) VN
  , "2"
  )

test15 = mkTest
  ( "Chk Enum('a, 'b, 'c): 'b + 2"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ Z
        tm = atom "b" + 2
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN)
  , Left "checkEnumEh: tag at index not determined."
  )

test16 = mkTest
  ( "Chk Enum('a, 'b, 'c): (x :: Atom)"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ S Z
        tm = evar 0
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN :# atom SAtom)
 , Left "TC monad"
 )

test17 = mkTest
  ( "Chk Enum('a, 'b, 'c): x :: Enum('a, 'b, 'c)"
  , let ty = mk SEnum atoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ S Z
        tm = evar 0
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN :# ty)
  , Right ()
  )

test18 = mkTest
  ( "Chk Enum('a, 'b, 'c): x :: Enum('a, 'b)"
  , let ty = mk SEnum atoms
        subty = mk SEnum subatoms
        atoms = (f "a" + f "b" + f "c") :: Term Chk ^ S Z
        subatoms = (f "a" + f "b") :: Term Chk ^ S Z
        tm = evar 0
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, VN :# subty)
  , Right ()
  )

test19 = mkTest
  ( "Chk Enum('a, 'b, 'c): y :: Enum(z + ('a, 'b, 'c))"
  , let zty = mk SList SAtom
        yty = mk SEnum (evar 2)
        xty = mk SEnum atoms
        ty  = mk SEnum (evar 2 + atoms)
        atoms = f "a" + f "b" + f "c"
        tm = evar 1
        ctx = VN :# zty :# yty :# xty
        f s = mk Sone (atom s)
    in runTC (checkEh ty tm) (natty, ctx)
  , Right ()
  )

test20 = mkTest
  ( "Ty Pi: lam (X : Type). lam (x : X) . x"
  , let ty = mk SPi SType (lam "X" body)
        body = mk SPi (evar 0) (lam "x" (evar 1))
    in runTC (typeEh ty) (natty, VN)
  , Right ()
  )

test21 = mkTest
  ( "Chk Pi: lam X x. x : (X : Type) -> (x : X) -> x"
  , let ty = mk SPi SType (lam "X" body)
        body = mk SPi (evar 0) (lam "x" (evar 1))
        tm = lam "X" $ lam "x" (evar 0)
    in runTC (checkEh ty tm) (natty, VN)
  , Right ()
  )

test22 = mkTest
  ( "Chk Pi: lam X f x. f (f x)"
  , let ty = mk SPi SType (lam "X" body)
        body = (evar 0 ==> evar 0) ==> (evar 0 ==> evar 0)
        tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 1 <&> evar 0)
    in runTC (checkEh ty tm) (natty, VN)
  , Right ()
  )

test23 = mkTest
  ( "Chk Pi: lam X f x : f (x x)"
  , let ty = mk SPi SType (lam "X" body)
        body = (evar 0 ==> evar 0) ==> (evar 0 ==> evar 0)
        tm = lam "X" $ lam "f" $ lam "x" $
              E $^ D $^ var 1 <&> (E $^ D $^ var 0 <&> evar 0)
    in runTC (checkEh ty tm) (natty, VN)
  , Left "synthEh: no"
  )

test24 = mkTest
  ( "EvalSyn Sig: (One, x)"
  , let ty = mk SSig SType (lam "X" (evar 0))
        tm = D $^ (R $^ (T $^ atom SOne <&> evar 0) <&> ty) <&> atom Ssnd
        ctx = VN :# ("x", atom SOne)
    in  testShowTC (fst <$> evalSynth tm) ctx
  , "[]"
  )
