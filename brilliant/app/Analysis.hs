-- | Some analyses

module Analysis where

import Bril
import Opt
import CFG (BB(..), successors, edges)
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict (Map)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.List
import Data.Maybe
import Data.Text qualified as T
import GHC.Stack (HasCallStack)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup
import Data.Tree
import Data.Foldable
import Control.Monad
import Control.Applicative

concatSemigroup :: (HasCallStack, Semigroup a) => [a] -> a
concatSemigroup (x:xs) = sconcat (x :| xs)
concatSemigroup [] = error "concatSemigroup: empty list"

-- | Dataflow analysis
--
-- Merge is given by the semigroup instance. We end up computing a lifted analysis
-- so we don't actually need a bottom element.
class (Eq a, Semigroup a) => Dataflow a where
  transfer :: BB -> a -> a

-- | For analyses that go instruction-by-instruction
transferInstr :: (Instr -> a -> a) -> (BB -> a -> a)
transferInstr f (BB _ _ is _) x = foldl' (flip f) x is

-- | Returns the values at all the entry nodes
forwardsAnalysis :: Dataflow a => Label -> a -> Map Label BB -> Map Label (a,a)
forwardsAnalysis entryLabel entryValue bbs =
    go mempty [entryLabel]
  where preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
        go m [] = m
        go m (l:ls) =
          let oldStart = fst <$> Map.lookup l m
              start = concatSemigroup $ (if l == entryLabel then [entryValue] else []) ++
                [a | pred <- fromMaybe [] $ Map.lookup l preds, Just (_,a) <- [Map.lookup pred m]]
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

instance VariableAnalysis a => Dataflow (PerVariable a) where
  transfer = transferInstr $ \i (PerVariable m) -> case instrDest i of
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

prettyConstProp :: PerVariable ConstLattice -> String
prettyConstProp (PerVariable m) =
    if Map.null m then "∅" else intercalate ", " [T.unpack v ++ ": " ++ pretty l | (v, l) <- Map.toList m]
  where pretty Top = "?"
        pretty (Value l) = prettyLit l
        prettyLit (IntLit x) = show x
        prettyLit (BoolLit b) = show b

-- | Compute all dominators using data flow
dominators :: Label -> Map Label BB -> Map Label (Set Label)
dominators entryLabel bbs = getDom . snd <$> forwardsAnalysis entryLabel (Dom mempty) bbs

newtype Dominators = Dom { getDom :: Set Label } deriving (Show, Eq, Ord)
instance Semigroup Dominators where
  Dom a <> Dom b = Dom (Set.intersection a b)
instance Dataflow Dominators where
  transfer (BB l _ _ _) (Dom a) = Dom (Set.insert l a)

-- | Assumes all blocks are reachable
buildDomFrontier :: Label -> Map Label BB -> Map Label (Set Label) -> Map Label (Set Label)
buildDomFrontier start bbs doms = Map.fromListWith Set.union
  [ (d, Set.singleton b) | (a,b) <- edges bbs, d <- Set.toList $ (doms Map.! a) Set.\\ (doms Map.! b) ]

buildDomTree :: Label -> Map Label (Set Label) -> Tree Label
buildDomTree start doms = go start
  where a `dominates` b = a `Set.member` (doms Map.! b)
        moreSpecific a b
          | a `dominates` b = b
          | b `dominates` a = a
          | otherwise = error "neither is more specific"
        parent (b,ds) = case filter (/= b) $ Set.toList ds of
          [] -> Nothing
          x:xs -> Just (b, foldl' moreSpecific x xs)
        children = Map.fromListWith (++) [(p, [b]) | Just (b, p) <- parent <$> Map.toList doms]
        go a = Node a [go b | b <- fromMaybe [] $ Map.lookup a children, b /= a]

dominatorTree :: Label -> Map Label BB -> Tree Label
dominatorTree start bbs = buildDomTree start (dominators start bbs)

domTreeOfOptFunction :: OptFunction -> Tree Label
domTreeOfOptFunction (OptFunction _ _ _ start bbs) = dominatorTree start bbs

-- | testing the dominators. slow
domFnIsGood :: Label -> Map Label BB -> (Label -> Label -> Bool) -> Bool
domFnIsGood start bbs claimedDom =
    and [claimedDom a b == dominates a b | a <- Map.keys bbs, b <- Map.keys bbs]
  where dominates a b = a == b || a == start || not (search (Set.singleton start) a b)
        -- is there a path from a to b not going through x?
        search a x b | b `Set.member` a = True
        search a x b =
          let a' = a `Set.union` Set.fromList [s | b <- Set.toList a, s <- successors (bbs Map.! b), s /= x]
          in a /= a' && search a' x b

dominatorsIsGood :: Label -> Map Label BB -> Map Label (Set Label) -> Bool
dominatorsIsGood start bbs doms =
  domFnIsGood start bbs (\a b -> a `Set.member` (doms Map.! b))

domTreeIsGood :: Label -> Map Label BB -> Tree Label -> Bool
domTreeIsGood start bbs tree =
    domFnIsGood start bbs (\a b -> (a,b) `Set.member` claimedPairs)
  where go (Node a bs) = [(a,a)] ++ [(a, b) | t <- bs, b <- toList t] ++ (bs >>= go)
        claimedPairs = Set.fromList (go tree)

