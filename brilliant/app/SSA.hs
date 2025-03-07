-- | To and from SSA

module SSA where

import Bril
import Opt
import CFG (BB(..), successors, edges)
import Analysis
import Util
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Map.Strict (Map)
import Data.Set qualified as Set
import Data.Set (Set)
import Data.List
import Data.Maybe
import Data.Text qualified as T
import Data.Semigroup
import Data.Tree
import Data.Foldable
import Data.Traversable
import Control.Monad
import Control.Applicative
import Control.Monad.State

-- TODO:
-- * if the fn reassigns args, toCFG should rename vars vs args + add a header block
-- * split critical edges
-- * compute (ssa) var live range conficts
-- * (greedy?) ssa var coalescing

-- | To SSA by adding phis in the dominance frontier
toSSA :: OptFunction -> OptFunction
toSSA (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start (fmap (\(_,bb,_) -> bb) result)
  where
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    doms = dominators start bbs
    domFrontier = buildDomFrontier start bbs doms
    df s = Set.unions [fromMaybe Set.empty $ Map.lookup l domFrontier | l <- Set.toList s]

    live = let m = liveVars start bbs in \l v -> v `Set.member` (m ! l)

    initialDefs :: [(Var, Set Label)]
    initialDefs = Map.toList $ Map.fromListWith Set.union
      [(v,Set.singleton l) | (l,bb) <- Map.toList bbs, v <- Set.toList $ varDefs bb]

    types :: Map Var Type
    types = Map.fromListWith (\x y -> if x == y then x else error "types don't match")
      [(v, t) | Dest v t <- getConst $ visitDefs (Const . pure) bbs]

    phis :: Map Label [Var]
    phis = Map.fromListWith (++)
      [(l, [v]) | (v, init) <- initialDefs, l <- Set.toList $ semiNaive (df init) (const df), live l v]
      `Map.union` fmap (const []) bbs

    fresh :: Var -> State Int Var
    fresh v = state \s -> (v <> "." <> T.pack (show s), s+1)

    result :: Map Label (Map Var Var, BB, Map Var Var)
    result = flip evalState 0 $ for bbs \bb@(BB l ls is t) -> do
      -- populate the initial env from the phis
      phiEnv <- Map.fromList <$> for (phis ! l) \v -> (v,) <$> fresh v

      -- make the initial environment from the final environment of the predecessors
      let env = case domTreeParent doms l of
            Nothing -> Map.fromList [(v,v) | Dest v _ <- params] -- the entry has no phis, just params (which are disjoint from program vars)
            Just p -> let (_, _, end) = result ! p in phiEnv `Map.union` end

      -- rename uses, defs
      (is', env') <- flip runStateT env $ for is \i -> do
        i' <- gets \e -> mapUses (e !) i
        flip visitDefs i' \(Dest v t) -> StateT \e -> do
          v' <- fresh v
          pure (Dest v' t, Map.insert v v' e)

      let t' = mapUses (env' !) t

      -- make the phis
      let gets = [Op (Dest (phiEnv ! v) (types ! v)) Get [] | v <- phis ! l]
          sets =
            [ Effect Set [end ! v, env' ! v]
            | s <- successors bb, v <- phis ! s, let (_, _, end) = result ! s]

      pure (env, BB l ls (gets ++ is' ++ sets) t', env')



