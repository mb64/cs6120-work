module Util where

import Data.Tuple
import Data.Map qualified as Map
import Data.Map (Map)
import Debug.Trace (trace)
import GHC.Stack (HasCallStack)

(!) :: (Ord k, Show k, HasCallStack) => Map k a -> k -> a
m ! k = case Map.lookup k m of
  Just v -> v
  Nothing -> error $ "key " ++ show k ++ " not in map!"

debug :: Show a => String -> a -> b -> b
debug msg x y = trace (msg ++ ": " ++ show x) y

getSolo :: Solo a -> a
getSolo (Solo a) = a

