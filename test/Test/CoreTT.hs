module Test.CoreTT where

import CoreTT
import Term hiding (testShow)
import Term.Natty
import Term.Vec
import NormalForm

import Test.Tasty(TestTree)
import Test.Tasty.HUnit

testCtx :: Vec (S (S (S Z))) String
testCtx = VN :# "z" :# "y" :# "x"

testShow :: Term ^ S (S (S Z)) -> String
testShow t = tmShow False t testCtx

mkTest :: (Eq a, Show a, HasCallStack) => (String, a, a) -> TestTree
mkTest (name, val, exp) = testCase name $ val @?= exp

coreTests :: [TestTree]
coreTests = [ test0, test1, test2, test3, test4, test5, test5', test6, test7
            , test8, test9, test10, test11, test12, test13, test14, test14'
            , test15, test16, test17, test18, test19
            ]

test0 = mkTest
        ( "Eval Abel (prop): x + y"
        , let ty = tup [TyAbel (no natty), TyOne (no natty)]
              tm = var 0 + var 1
          in testShow $ checkEval ty tm
        , "['plus y x]"
        )

test1 = mkTest
        ( "Eval Abel (prop): y + x"
        , let ty = tup [TyAbel (no natty), TyOne (no natty)]
              tm = var 1 + var 0
          in testShow $ checkEval ty tm
        , "['plus y x]"
        )

test2 = mkTest
        ( "Eval Abel (prop): x + x"
        , let ty = tup [TyAbel (no natty), TyOne (no natty)]
              tm = var 0 + var 0
          in testShow $ checkEval ty tm
        , "[2 x]"
        )

test3 = mkTest
        ( "Eval Abel (prop): x + 3 + x"
        , let ty = tup [TyAbel (no natty), TyOne (no natty)]
              tm = (var 0 + 3) + var 0
          in testShow $ checkEval ty tm
        , "['plus 3 [2 x]]"
        )

test4 = mkTest
        ( "Eval Abel (prop): 1::int 5"
        , let ty = tup [TyAbel (no natty), TyOne (no natty)]
              tm = tup [One (no natty), int 5]
          in testShow $ checkEval ty tm
        , "1"
        )

test5 = mkTest
        ( "Eval List (prop): x + y"
        , let ty = tup [TyList (no natty), TyOne (no natty)]
              tm = var 0 + var 1
          in testShow $ checkEval ty tm
        , "['plus y x]"
        )

test5' = mkTest
         ( "Eval List (non-prop): x + y"
         , let ty = tup [TyList (no natty), TyU(no natty)]
               tm = var 0 + var 1
           in testShow $ checkEval ty tm
         , "['plus x y]"
         )

test6 = mkTest
        ( "Eval List (prop): y + x"
        , let ty = tup [TyList (no natty), TyOne (no natty)]
              tm = var 1 + var 0
          in testShow $ checkEval ty tm
        , "['plus y x]"
        )

test7 = mkTest
        ( "Eval List (prop): x + 3 + x"
        , let ty = tup [TyList (no natty), TyOne (no natty)]
              tm = (var 0 + 3) + var 0
          in testShow $ checkEval ty tm
        , "['plus 3 [2 x]]"
        )

test8 = mkTest
        ( "TC List (prop): x + 3 + x"
        , let ty = tup [TyList (no natty), TyOne (no natty)]
              tm = (var 0 + 3) + var 0
              ctx = VN :# ty :# ty :# ty
          in runTC (checkEh ty tm) (natty, ctx)
        , Right ()
        )

test9 = mkTest
        ( "TC List (prop): x - 3 + x"
        , let ty = tup [TyList (no natty), TyOne (no natty)]
              tm = var 0 + (-3) + var 0
              ctx = VN :# ty :# ty :# ty
          in runTC (checkEh ty tm) (natty, ctx)
        , Left "checkEh: Negative length list"
        )

test10 = mkTest
         ( "TC Enum('a, 'b, 'c): 'a"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = At "a"
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )

test11 = mkTest
         ( "TC Enum('a, 'b, 'c): 'd"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = At "d"
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Left "checkEnumEh: position of atom 'd not determined."
         )

test12 = mkTest
         ( "TC Enum('a, 'b, 'c): 2"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = int 2
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )

test13 = mkTest
         ( "TC Enum('a, 'b, 'c): 5"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = int 5
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Left "checkEnumEh: tag at index not determined."
         )

test14 = mkTest
         ( "TC Enum('a, 'b, 'c): 'b + 1"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = At "b" + 1
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )

test14' = mkTest
          ( "Eval Enum('a, 'b, 'c): 'b + 1"
          , let ty = tup [TyEnum (no natty), atoms]
                atoms = f "a" + f "b" + f "c"
                tm = At "b" + 1
                f s = tup [One (no natty), At s]
            in testShow $ checkEval ty tm
          , "2"
          )

test15 = mkTest
         ( "TC Enum('a, 'b, 'c): 'b + 2"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = At "b" + 2
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Left "checkEnumEh: tag at index not determined."
         )

test16 = mkTest
         ( "TC Enum('a, 'b, 'c): (x :: Atom)"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = var 0
               ctx = VN :# cty :# cty :# cty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
        , Left "sameEh : different terms."
        )

test17 = mkTest
         ( "TC Enum('a, 'b, 'c): x :: Enum('a, 'b, 'c)"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               atoms = f "a" + f "b" + f "c"
               tm = var 0
               ctx = VN :# cty :# cty :# ty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )

test18 = mkTest
         ( "TC Enum('a, 'b, 'c): x :: Enum('a, 'b)"
         , let cty = TyAtom (no natty)
               ty = tup [TyEnum (no natty), atoms]
               subty = tup [TyEnum (no natty), subatoms]
               atoms = f "a" + f "b" + f "c"
               subatoms = f "a" + f "b"
               tm = var 0
               ctx = VN :# cty :# cty :# subty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )

test19 = mkTest
         ( "TC Enum('a, 'b, 'c): y :: Enum(z + ('a, 'b, 'c))"
         , let cty = TyAtom (no natty)
               zty = tag SList [cty]
               yty = tup [TyEnum (no natty), var 2]
               xty = tup [TyEnum (no natty), atoms]
               ty  = tup [TyEnum (no natty), var 2 + atoms]
               atoms = f "a" + f "b" + f "c"
               tm = var 1
               ctx = VN :# zty :# yty :# xty
               f s = tup [One (no natty), At s]
           in runTC (checkEh ty tm) (natty, ctx)
         , Right ()
         )
