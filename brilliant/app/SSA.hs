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
import Data.Functor.Identity
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

-- | Stupid and simple, because the better one is too much thinking for now
--
-- Takes a list of (dest,src)
parallelMove :: Map Var Type -> [(Var, Var)] -> [Instr]
parallelMove types moves = 
    if Set.disjoint targets sources then fastVersion else slowVersion
  where
    targets = Set.fromList $ map fst moves
    sources = Set.fromList $ map snd moves

    copy t v v' = Op (Dest v t) Id [v']
    fastVersion = [copy (types!v) v v' | (v,v') <- moves]
    slowVersion = [copy (types!v') (v' <> ".tmp") v' | v' <- Set.toList sources]
      ++ [copy (types!v) v (v' <> ".tmp") | (v,v') <- moves]

-- | Do some coalescing and some parallel moves
--
-- FIXME: I think there's a possible bug due to not splitting critical edges
fromSSA :: OptFunction -> OptFunction
fromSSA (OptFunction name params retTy start bbs) =
    OptFunction name (rename params) retTy start (handleBB <$> bbs)
  where
    types = getTypes params bbs

    -- compute liveness: very coarse, just by block
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    usesInst (Effect Set [_,v]) = Set.singleton v
    usesInst i = varUses i
    usesBB (BB _ _ is t) = varUses t `Set.union` foldMap usesInst is
    allDefs = Set.fromList [(v,l) | (l,b) <- Map.toList bbs, v <- Set.toList (varDefs b)]
    allUses = Set.fromList [(v,l) | (l,b) <- Map.toList bbs, v <- Set.toList (usesBB b)]
    livePairs = semiNaive allUses $ \_ d -> Set.fromList
      [ (v,p) | (v,l) <- Set.toList d
      , not $ (v,l) `Set.member` allDefs, p <- fromMaybe [] $ Map.lookup l preds]
    liveByVar = Map.fromListWith Set.union [(v,Set.singleton l) | (v,l) <- Set.toList livePairs]

    -- try merging things with disjoint live ranges
    desiredMerges = [(v,v') | (_,BB _ _ is _) <- Map.toList bbs, Effect Set [v,v'] <- is]
    find x m = case Map.lookup x m of
      Just (Left x') -> find x' m
      Just (Right v) -> (x,v)
      Nothing -> (x,Set.empty)
    union x y v m = Map.insert x (Right v) $ Map.insert y (Left x) m
    coalesce m [] = m
    coalesce m ((x,y):xs)
      | (x',vx) <- find x m, (y',vy) <- find y m
      , Set.disjoint vx vy = coalesce (union x' y' (Set.union vx vy) m) xs
      | otherwise = coalesce m xs
    finalM = coalesce (Right <$> liveByVar) desiredMerges
    rename :: forall a. Code a => a -> a
    rename = runIdentity . visit (visitVars (\v -> pure $ fst $ find v finalM))

    -- translate all the phi's to parallel-move's in the predecessor blocks
    handleBB (BB l ls is t) =
      let (_,i,s) = splitPhisBB (rename is)
          move = parallelMove types [(v,v') | Effect Set [v,v'] <- s, v /= v']
      in BB l ls (i ++ move) (rename t)

-- | Copy propagation + DCE. Only run it on SSA form!
--
-- TODO: DCE
ssaCopyPropagate :: OptFunction -> OptFunction
ssaCopyPropagate (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start (process <$> bbs)
  where values = Map.fromListWith (error "not SSA")
          [(v,v') | (_,BB _ _ is _) <- Map.toList bbs, Op (Dest v _) Id [v'] <- is]
        find v | v `Map.member` values = find (values ! v)
               | otherwise = v
        shouldKeep (Op _ Id _) = False -- never keep copies
        shouldKeep _ = True
        process (BB l ls is t) =
          mapUses find $ BB l ls (filter shouldKeep is) t

-- | Split into gets, normal instructions, and sets
splitPhisBB :: [Instr] -> ([Instr], [Instr], [Instr])
splitPhisBB = foldMap f
  where f i@(Op _ Get _) = ([i], [], [])
        f i@(Effect Set _) = ([], [], [i])
        f i = ([], [i], [])

-- | The defining block of all variables
--
-- This is well-defined when you're in SSA since there's only one def
definingBlocks :: Map Label BB -> Map Var Label
definingBlocks bbs = Map.fromListWith (error "not in SSA!")
  [(v, l) | (l, BB _ _ is _) <- Map.toList bbs, v <- Set.toList $ varDefs is]

-- | This is here cuz merging blocks deals with the phi's appropriately.
cleanUpCFG :: OptFunction -> OptFunction
cleanUpCFG (OptFunction name params out start bbs) =
    cfgDeadCodeElim $ OptFunction name params out start bbs'
  where bbs' = mergeBlocks start $ removeEmptyBlocks start bbs

-- | Remove empty basic blocks
--
-- TODO: handle blocks with just phi's in them
removeEmptyBlocks :: Label -> Map Label BB -> Map Label BB
removeEmptyBlocks start bbs = Map.fromList
    [(l,BB l [] is (rename t)) | (l,BB _ _ is t) <- Map.toList bbs, l `Map.notMember` fws]
  where fws = Map.fromList [(l,l') | (l,BB _ _ [] (Jmp l')) <- Map.toList bbs, l /= start]
        find l = maybe l find $ Map.lookup l fws
        rename = runIdentity . visit (defaultVisitor { visitLabel = pure . find })

-- | Merge basic blocks
mergeBlocks :: Label -> Map Label BB -> Map Label BB
mergeBlocks start bbs = Map.fromList
    [(l,lengthen bb) | (l,bb) <- Map.toList bbs, not $ willGetMerged l]
  where
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    hasUniquePred b = b /= start && length (preds ! b) == 1
    willGetMerged b = b /= start && case preds ! b of
      [p] -> length (successors (bbs ! p)) == 1
      _ -> False

    lengthen bb = case successors bb of
      [s] | hasUniquePred s -> lengthen (mergeBBs bb (bbs ! s))
      _ -> bb

    mergeBBs (BB l _ is _) (BB _ _ is' t) =
      let (g, i, s) = splitPhisBB is
          (g', i', s') = splitPhisBB is'
      in BB l [] (g ++ g' ++ i ++ i' ++ s ++ s') t

