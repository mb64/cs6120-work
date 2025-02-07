module Main where

import Bril
import CFG (buildCFG, wellFormedCFG)
import Opt
import qualified Data.Text.IO as T
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Decoding
import Control.Monad
import Data.Foldable

loadJSON :: IO Program
loadJSON = do
  Just (json :: Value) <- decodeStrictText <$> T.getContents
  case fromJSON json of
    Success x -> pure x
    Error msg -> fail msg

-- | Verify that the program round-trips as JSON successfully
testJSONRoundTrip :: Program -> IO ()
testJSONRoundTrip (Program fs) = do
  for_ fs \(Function _ _ _ code) -> do 
    for_ code \i -> do
      when (fromJSON (toJSON i) /= Success i) $ do
        BSL.putStr $ encode i
        putStrLn ""
        print $ fromJSON @Instr (toJSON i)
  let prog = Program fs
  when (fromJSON (toJSON prog) /= Success prog) $ do
    BSL.putStr $ encode prog
    putStrLn ""
    print $ fromJSON @Program (toJSON prog)
    fail "mismatch"

-- | Validate that the CFG we make is a valid CFG
validateCFG :: Program -> IO ()
validateCFG (Program fs) = for_ fs \(Function _ _ _ code) -> do
  let cfg = buildCFG code
  -- putStrLn "CFG is:"
  -- print cfg
  case wellFormedCFG cfg of
    Left msg -> fail $ "got a bad CFG: " ++ msg
    Right () -> pure ()

main :: IO ()
main = do
  prog <- loadJSON

  -- For now, include a bunch of assertions...
  testJSONRoundTrip prog
  validateCFG prog

  -- ...even though the actual task is to run optimizations
  let optimize = fromOptFunction . cfgDeadCodeElim . tdce . lvn . toOptFunction
      optimizeProg (Program fs) = Program (map optimize fs)

  BSL.putStr $ encode $ optimizeProg prog
  putStrLn ""
