-- | Some analyses

module Analysis where

import Bril
import Opt
import CFG (BB(..), successors)
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict (Map)
import Data.List
import Data.Maybe

-- | Dataflow analysis
--
-- Merge, init is given by the monoid instance
class (Eq a, Monoid a) => Dataflow a where
  transferInstr :: Instr -> a -> a
  transfer :: BB -> a -> a
  transfer (BB _ _ is _) x = foldl' (flip transferInstr) x is

-- | Returns the values at all the entry nodes
forwardsAnalysis :: (Show a, Dataflow a) => Label -> a -> Map Label BB -> Map Label (a,a)
forwardsAnalysis entryLabel entryValue bbs =
    go mempty [entryLabel]
  where preds = Map.fromListWith (++) [(s,[l]) | (l,bb) <- Map.toList bbs, s <- successors bb]
        go m [] = m
        go m (l:ls) =
          let oldStart = fst <$> Map.lookup l m
              start_ = mconcat [a | pred <- fromMaybe [] $ Map.lookup l preds, Just (_,a) <- [Map.lookup pred m]]
              start = if l == entryLabel then entryValue <> start_ else start_
              bb = bbs Map.! l
          in if oldStart == Just start then
              go m ls
          else
              go (Map.insert l (start, transfer bb start) m) (successors bb ++ ls)

-- | Per-variable analysis
class (Show a, Eq a) => VariableAnalysis a where
  merge :: Maybe a -> Maybe a -> Maybe a
  instr :: Map Var a -> Instr -> Maybe a

newtype PerVariable a = PerVariable (Map Var a) deriving (Show, Eq, Ord)

instance VariableAnalysis a => Semigroup (PerVariable a) where
  PerVariable m1 <> PerVariable m2 = PerVariable $
    Map.merge (Map.mapMaybeMissing (\_ x -> merge (Just x) Nothing))
              (Map.mapMaybeMissing (\_ x -> merge Nothing (Just x)))
              (Map.zipWithMaybeMatched (\_ x y -> merge (Just x) (Just y)))
              m1 m2

instance VariableAnalysis a => Monoid (PerVariable a) where
  mempty = PerVariable mempty
  mappend = (<>)

instance VariableAnalysis a => Dataflow (PerVariable a) where
  transferInstr i (PerVariable m) = case instrDest i of
    Just (Dest v _) -> PerVariable $ Map.alter (\_ -> instr m i) v m
    Nothing -> PerVariable m

-- | Constant propagation
data ConstLattice = Top | Value Lit deriving (Show, Eq, Ord)

instance VariableAnalysis ConstLattice where
  merge Nothing x = x
  merge x Nothing = x
  merge (Just x) (Just y) = Just $ if x == y then x else Top

  instr _ (Constant _ l) = Just (Value l)
  instr m (Op _ op args) =
    case traverse (\x -> Map.lookup x m >>= \case { Top -> Nothing ; Value l -> Just l }) args >>= evalOp op of
      Just l -> Just (Value l)
      Nothing -> Just Top
  instr m _ = Just Top

-- | Putting it all together...
analyzeConstProp :: OptFunction -> Map Label (PerVariable ConstLattice, PerVariable ConstLattice)
analyzeConstProp (OptFunction _ params _ startLabel bbs) =
  let init = PerVariable $ Map.fromList [(x,Top) | Dest x _ <- params]
  in forwardsAnalysis startLabel init bbs


