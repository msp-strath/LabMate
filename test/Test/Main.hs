module Main where

import Control.Monad

import Data.List ((\\), isPrefixOf)

import System.Directory
import System.FilePath

import Test.Tasty (TestTree,testGroup)
import Test.Tasty.Silver
import Test.Tasty.Silver.Interactive
import Test.Tasty.HUnit

import Test.CoreTT

data TestConfig = TestConfig
  { name         :: String
  , extension    :: String
  , goldenExt    :: String
  , goldenDir    :: String
  , folder       :: FilePath
  , excluded     :: [FilePath]
  , excludedDirs :: [FilePath]
  }

main :: IO ()
main = defaultMain . testGroup "LabMate" =<< sequence
  [ examples
  , coreTTTests
  ]

examples :: IO TestTree
examples = do
  let name      = "Examples"
  let extension = ".m"
  let goldenExt = ".gold"
  let folder    = "examples"
  let goldenDir = "test/golden"
  let excluded  = []
  let excludedDirs = [folder </> "npl"]
  ioTests TestConfig{..}


coreTTTests :: IO TestTree
coreTTTests = do
 let name = "CoreTT"
 pure $ testGroup name coreTests

ioTests :: TestConfig -> IO TestTree
ioTests TestConfig{..} = testGroup name <$> do
  files <- map normalise <$> findByExtension [extension] folder
  let excludedFiles = normalise . (folder </>) <$> excluded
  forM (filter (\ f -> not (any (`isPrefixOf` f) excludedDirs)) $ files \\ excludedFiles) $ \ file -> do
    let dir  = takeDirectory file
    let name = takeBaseName file
    let gold = goldenDir </> addExtension name goldenExt
    let flgs = dir </> addExtension name "flags"
    b <- doesFileExist flgs
    flags <- if b then words <$> readFile flgs else pure ["--no-version"]
    pure $ goldenVsProg name gold "labmate" (flags ++ [file]) ""
