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

getTypes :: Code a => [Dest] -> a -> Map Var Type
getTypes params code = Map.fromListWith (\x y -> if x == y then x else error "types don't match")
  [(v, t) | Dest v t <- params ++ (getConst $ visitDefs (Const . pure) code)]

-- | To SSA, by adding phis in the dominance frontier
toSSA :: OptFunction -> OptFunction
toSSA (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start (fmap (\(_,bb,_) -> bb) result)
  where
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    doms = dominators start bbs
    domFrontier = buildDomFrontier start bbs doms
    df s = Set.unions [fromMaybe Set.empty $ Map.lookup l domFrontier | l <- Set.toList s]
    types = getTypes params bbs
    live = let m = liveVars start bbs in \l v -> v `Set.member` (m ! l)

    -- figure out which phis to add where
    phis :: Map Label [Var]
    phis = Map.fromListWith (++)
      [(l, [v]) | (v, init) <- initialDefs, l <- Set.toList $ semiNaive (df init) (const df), live l v]
      `Map.union` fmap (const []) bbs

    initialDefs :: [(Var, Set Label)]
    initialDefs = Map.toList $ Map.fromListWith Set.union
      [(v,Set.singleton l) | (l,bb) <- Map.toList bbs, v <- Set.toList $ varDefs bb]

    -- update the code
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
            [ Effect Set [phiE ! v, env' ! v]
            | s <- successors bb, v <- phis ! s, let (phiE, _, _) = result ! s]

      pure (phiEnv, BB l ls (gets ++ is' ++ sets) t', env')

-- | Stupid and simple, because I didn't have time to implement a better one
--
-- Ideally I would be doing some coalescing
fromSSA :: OptFunction -> OptFunction
fromSSA (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start (fmap bb bbs)
  where bb (BB l ls is t) = BB l ls (map inst is) t
        inst (Op (Dest v t) Get _) = Op (Dest v t) Id [v <> ".shadow"]
        inst (Effect Set [v,v']) = Op (Dest (v <> ".shadow") (types ! v')) Id [v']
        inst x = x
        types = getTypes params bbs

-- | Copy propagation. Only run it on SSA form!
ssaCopyPropagate :: OptFunction -> OptFunction
ssaCopyPropagate (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start (process <$> bbs)
  where values = Map.fromListWith (error "not SSA")
          [(v,v') | (_,BB _ _ is _) <- Map.toList bbs, Op (Dest v _) Id [v'] <- is]
        find v | v `Map.member` values = find (values ! v)
               | otherwise = v
        isNotCopy (Op _ Id _) = False
        isNotCopy _ = True
        process (BB l ls is t) =
          mapUses find $ BB l ls (filter isNotCopy is) t

