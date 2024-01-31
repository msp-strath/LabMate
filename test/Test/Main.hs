{- AUTOCOLLECT.MAIN
custom_main = True
group_type = flat
-}

module Main where

import Test.Tasty hiding (defaultMain)
import Test.Tasty.Silver.Interactive

import Test.CoreTT as CoreTT
{- AUTOCOLLECT.MAIN.imports -}
import Test.Golden

main :: IO ()
main = do
  core <- coreTT
  gold <- examples
  let tests = testGroup "LabMate" [core, gold]
  defaultMain tests

coreTT :: IO TestTree
coreTT = pure $ testGroup "CoreTT" tests
  where
    tests = id {- AUTOCOLLECT.MAIN.tests -}

examples :: IO TestTree
examples =
  let extension = ".m"
      goldenExt = ".gold"
      folder    = "examples"
      goldenDir = "test/golden"
      excluded  = []
      excludedDirs = [folder </> "npl"]
  in testGroup "Examples" <$> ioTests TestConfig{..}
