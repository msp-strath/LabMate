{- AUTOCOLLECT.MAIN
custom_main = True
group_type = flat
-}

module Main where

import Debug.Trace
import Test.Tasty

import Test.CoreTT as CoreTT
{- AUTOCOLLECT.MAIN.imports -}

debug = trace

coreTT :: IO TestTree
coreTT = do
  let t = tests
  pure $ testGroup "CoreTT" (debug ("Show " ++ show (length t)) t)
  where
    tests = id {- AUTOCOLLECT.MAIN.tests -}

main :: IO ()
main = coreTT >>= defaultMain
