module Main where

import System.FilePath
import System.Directory

import Control.Monad

import Data.List ((\\), isPrefixOf)

import Test.Tasty hiding (defaultMain)
import Test.Tasty.Silver
import Test.Tasty.Silver.Interactive

data TestConfig = TestConfig
  { extension    :: String
  , goldenExt    :: String
  , goldenDir    :: String
  , folder       :: FilePath
  , excluded     :: [FilePath]
  , excludedDirs :: [FilePath]
  }

examples :: IO TestTree
examples =
  let extension = ".m"
      goldenExt = ".gold"
      folder    = "examples"
      goldenDir = "test/golden"
      excluded  = []
      excludedDirs = [folder </> "npl"]
  in testGroup "Examples" <$> ioTests TestConfig{..}

ioTests :: TestConfig -> IO [TestTree]
ioTests TestConfig{..} = do
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


main :: IO ()
main = examples >>= defaultMain
