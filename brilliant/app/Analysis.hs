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
import Data.List hiding (union)
import Data.Maybe
import Data.Text qualified as T
import GHC.Stack (HasCallStack)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Semigroup
import Data.Tree
import Data.Foldable
import Data.Coerce
import Control.Monad
import Control.Applicative hiding (empty)

class Lattice a where
  merge :: a -> a -> a

instance Ord a => Lattice (Set a) where
  merge = Set.union

instance (Lattice a, Lattice b) => Lattice (a, b) where
  merge (x, y) (z, w) = (merge x z, merge y w)

instance (Ord k, Lattice a) => Lattice (Map k a) where
  merge =
    Map.merge Map.preserveMissing Map.preserveMissing (Map.zipWithMatched (\_ x y -> merge x y))

class Lattice a => Pointed a where
  empty :: a
  isEmpty :: a -> Bool

instance Ord a => Pointed (Set a) where
  empty = Set.empty
  isEmpty = Set.null

instance (Pointed a, Pointed b) => Pointed (a, b) where
  empty = (empty, empty)
  isEmpty (a,b) = isEmpty a && isEmpty b

instance (Ord k, Lattice a) => Pointed (Map k a) where
  empty = Map.empty
  isEmpty = Map.null

checkEmpty :: Pointed a => a -> Maybe a
checkEmpty x = if isEmpty x then Nothing else Just x

-- | Semi-naive Datalog evaluation
--
-- semiNaive orig f returns the least value containing orig and closed under f
--
-- f should be monotone. it's ok if f is not strict
semiNaive :: Datalog a => a -> (a -> a -> a) -> a
semiNaive orig f = iter orig orig
  where
    iter whole diff = let new = f whole diff in case new `without` whole of
      Nothing -> whole
      Just diff' -> iter (new `merge` whole) diff'

class (Eq a, Lattice a) => Datalog a where
  without :: a -> a -> Maybe a

newtype Naive a = Naive { getNaive :: a } deriving (Show, Eq, Ord, Lattice, Pointed)

instance (Eq a, Lattice a) => Datalog (Naive a) where
  x `without` y = if x == y then Nothing else Just x

instance Ord a => Datalog (Set a) where
  a `without` b = checkEmpty $ a Set.\\ b

instance (Ord k, Datalog a) => Datalog (Map k a) where
  m1 `without` m2 =
    checkEmpty $ Map.merge Map.preserveMissing Map.dropMissing (Map.zipWithMaybeMatched (\_ x y -> x `without` y)) m1 m2

instance (Datalog a, Pointed a, Datalog b, Pointed b) => Datalog (a, b) where
  (a,x) `without` (b,y) = case (a `without` b, x `without` y) of
    (Just c, Just z) -> Just (c,z)
    (Just c, Nothing) -> Just (c, empty)
    (Nothing, Just z) -> Just (empty, z)
    (Nothing, Nothing) -> Nothing

-- | Dataflow analysis
--
-- Merge is given by the semigroup instance. We end up computing a lifted analysis
-- so we don't actually need a bottom element.
class (Pointed a, Datalog a) => Dataflow a where
  transfer :: BB -> a -> a

-- | For analyses that go instruction-by-instruction
transferInstr :: (Instr -> a -> a) -> (BB -> a -> a)
transferInstr f (BB _ _ is _) x = foldl' (flip f) x is

-- | Returns the values at (entry, exit) of the basic blocks
forwardsAnalysis :: Dataflow a => Label -> a -> Map Label BB -> Map Label (a,a)
forwardsAnalysis start entryValue bbs = semiNaive init f
  where
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    init = Map.singleton start (entryValue, transfer (bbs Map.! start) entryValue)
    f m diff = Map.fromList
      [ (s, (v, transfer (bbs Map.! s) v))
      | (l,_) <- Map.toList diff, s <- successors (bbs Map.! l)
      , let v = foldl1' merge [snd (m Map.! p) | p <- preds Map.! s] ]

-- | Constant propagation
data ConstLattice = Value Lit | Top deriving (Show, Eq, Ord)

instance Lattice ConstLattice where
  x `merge` y = if x == y then x else Top

instance Dataflow (Naive (Map Var ConstLattice)) where
  transfer = transferInstr $ \i (Naive m) -> case instrDest i of
      Just (Dest v _) -> Naive $ Map.alter (\_ -> instr m i) v m
      Nothing -> Naive m
    where instr _ (Constant _ l) = Just (Value l)
          instr m (Op _ op args) =
            case traverse (\x -> Map.lookup x m >>= \case { Top -> Nothing ; Value l -> Just l }) args >>= evalOp op of
              Just l -> Just (Value l)
              Nothing -> Just Top
          instr m _ = Just Top

-- | Putting it all together...
analyzeConstProp :: OptFunction -> Map Label (Map Var ConstLattice, Map Var ConstLattice)
analyzeConstProp (OptFunction _ params _ startLabel bbs) =
  let init = Map.fromList [(x,Top) | Dest x _ <- params]
  in coerce $ forwardsAnalysis startLabel (Naive init) bbs

prettyConstProp :: Map Var ConstLattice -> String
prettyConstProp m =
    if Map.null m then "∅" else intercalate ", " [T.unpack v ++ ": " ++ pretty l | (v, l) <- Map.toList m]
  where pretty Top = "?"
        pretty (Value (IntLit x)) = show x
        pretty (Value (BoolLit b)) = show b

-- | Variables used within this basic block that need to be live at entry
usedVarsBB :: BB -> Set Var
usedVarsBB (BB _ _ is b) =
  foldr (\i s -> (s Set.\\ varDefs i) `Set.union` varUses i) (varUses b) is

-- | Live variables, at the start of each basic block
liveVars :: Label -> Map Label BB -> Map Label (Set Var)
liveVars start bbs = semiNaive (usedVarsBB <$> bbs) f
  where preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
        defs = fmap varDefs bbs
        -- TODO: if this infinite loops, fix it
        f _ diff = Map.fromList
          [(p, vars Set.\\ (defs Map.! p)) | (l, vars) <- Map.toList diff, p <- fromMaybe [] $ Map.lookup l preds]

-- | Compute all dominators using data flow
dominators :: Label -> Map Label BB -> Map Label (Set Label)
dominators start bbs =
    getDom <$> semiNaive (Map.singleton start (Dom Set.empty)) f
  where preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
        f m diff = Map.fromList
          [ (l, Dom $ Set.insert l $ foldl1' Set.intersection [getDom (m Map.! p) | p <- preds Map.! l])
          | (b,_) <- Map.toList diff, l <- successors (bbs Map.! b) ]

newtype Dominators = Dom { getDom :: Set Label } deriving (Show, Eq, Ord)
instance Lattice Dominators where
  Dom a `merge` Dom b = Dom (Set.intersection a b)
instance Datalog Dominators where
  Dom a `without` Dom b = if a == b then Nothing else Just (Dom a)

-- | Assumes all blocks are reachable
buildDomFrontier :: Label -> Map Label BB -> Map Label (Set Label) -> Map Label (Set Label)
buildDomFrontier start bbs doms = Map.fromListWith Set.union
  [(d, Set.singleton b) | (a,b) <- edges bbs, d <- Set.toList $ (doms Map.! a) Set.\\ (doms Map.! b)]

domTreeParent :: Map Label (Set Label) -> Label -> Maybe Label
domTreeParent doms l = case filter (/= l) $ Set.toList (doms Map.! l) of
    [] -> Nothing
    x:xs -> Just (foldl' moreSpecific x xs)
  where moreSpecific a b = if a `Set.member` (doms Map.! b) then b else a

-- TODO clean up
buildDomTree :: Label -> Map Label (Set Label) -> Tree Label
buildDomTree start doms = go start
  where moreSpecific a b = if a `Set.member` (doms Map.! b) then b else a
        parent (b,ds) = case filter (/= b) $ Set.toList ds of
          [] -> Nothing
          x:xs -> Just (b, foldl' moreSpecific x xs)
        children = Map.fromListWith (++) [(p, [b]) | Just (b, p) <- parent <$> Map.toList doms]
        go a = Node a [go b | b <- fromMaybe [] $ Map.lookup a children, b /= a]

dominatorTree :: Label -> Map Label BB -> Tree Label
dominatorTree start bbs = buildDomTree start (dominators start bbs)

-- | testing the dominators. slow
domFnIsGood :: Label -> Map Label BB -> (Label -> Label -> Bool) -> Bool
domFnIsGood start bbs claimedDom =
    and [claimedDom a b == dominates a b | a <- Map.keys bbs, b <- Map.keys bbs]
  where dominates a b = a == b || a == start || not (search (Set.singleton start) a b)
        -- is there a path from a to b not going through x?
        search a x b = b `Set.member` a || (a /= a' && search a' x b)
          where a' = a `Set.union` Set.fromList [s | b <- Set.toList a, s <- successors (bbs Map.! b), s /= x]

dominatorsIsGood :: Label -> Map Label BB -> Map Label (Set Label) -> Bool
dominatorsIsGood start bbs doms =
  domFnIsGood start bbs (\a b -> a `Set.member` (doms Map.! b))

domTreeIsGood :: Label -> Map Label BB -> Tree Label -> Bool
domTreeIsGood start bbs tree =
    domFnIsGood start bbs (\a b -> (a,b) `Set.member` claimedPairs)
  where go (Node a bs) = [(a,a)] ++ [(a, b) | t <- bs, b <- toList t] ++ (bs >>= go)
        claimedPairs = Set.fromList (go tree)

