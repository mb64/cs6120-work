module Main where

import Bril
import CFG (buildCFG, wellFormedCFG)
import Opt
import Analysis
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Decoding
import Data.List
import Control.Monad
import Data.Foldable
import Data.Tree (drawTree)

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

  -- ...even though the actual task is to do an analysis
  let optimize = fromOptFunction . cfgDeadCodeElim . tdce . lvn . toOptFunction
      _optimizeProg (Program fs) = Program (map optimize fs)
      _analyzeProg (Program fs) = for_ fs \f ->
        for_ (Map.toList $ analyzeConstProp $ toOptFunction f) \(lbl,(ins,outs)) -> do
          putStrLn $ T.unpack lbl ++ " in: \t" ++ prettyConstProp ins
          putStrLn $ T.unpack lbl ++ " out:\t" ++ prettyConstProp outs
      domTreesProg (Program fs) = for_ fs \f -> do
        let OptFunction name _ _ start bbs = cfgDeadCodeElim $ toOptFunction f
            doms = dominators start bbs
            tree = dominatorTree start bbs
        -- Print the dominator tree
        putStrLn $ "For function " ++ T.unpack name ++ ":"
        putStrLn $ drawTree $ fmap T.unpack tree

        -- Verify that the dominator computation is good
        unless (domTreeIsGood start bbs tree) $ fail "dom tree bad!"
        unless (dominatorsIsGood start bbs doms) $ fail "dominators bad!"

  -- BSL.putStr $ encode $ optimizeProg prog
  -- putStrLn ""

  -- analyzeProg prog

  domTreesProg prog
