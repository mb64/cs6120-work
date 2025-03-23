-- | Loop optimization!

module Loop where

import Bril
import Opt
import CFG (BB(..), successors, edges)
import Analysis
import SSA
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
import Data.Tuple
import Data.Foldable
import Data.Traversable
import Data.Functor.Identity
import Control.Monad
import Control.Applicative
import Control.Monad.State

-- Loop pre-header header-label header body
data LoopyNode = Loop BB Label BB (Map Label LoopyNode) | NonLoop BB deriving (Show, Eq)

-- | Build the loop tree, creating pre-headers for all loops.
--
-- Does not put it in LCSSA form. Maybe it should though? IDK
buildLoopTree :: Label -> Map Label BB -> Map Label LoopyNode
buildLoopTree start bbs = root
  where
    doms = dominators start bbs
    preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
    x `dominates` y = x `Set.member` (doms ! y)
    defBlocks = definingBlocks bbs

    -- find all loops: (header, block in that loop) pairs
    backEdges = Set.fromList [(h,b) | (b,h) <- edges bbs, h `dominates` b]
    headers = Set.fromList [h | (h,_) <- Set.toList backEdges]
    loops = semiNaive backEdges (\_ s ->
      Set.fromList [(h, p) | (h, b) <- Set.toList s, p <- preds ! b, h `dominates` p])

    moreSpecific x y = if x `dominates` y then y else x
    loopTreeParents = Map.fromListWith moreSpecific [(b,h) | (h,b) <- Set.toList loops, h /= b]

    -- Map a phi var to ([outside loop bbs], [inside loop bbs]) where it's set
    setBlocks = Map.fromListWith (<>)
      [ (v, if (defBlocks!v, l) `Set.member` loops then ([], [l]) else ([(l,v')], []))
      | (l, BB _ _ is _) <- Map.toList bbs, Effect Set [v,v'] <- is]

    -- rename (or remove!) all loop-external set's in cases when we add a new phi
    renameSet l i@(Effect Set [v, v']) = case setBlocks ! v of
      (ext@(_:_:_), _:_) | l `elem` map fst ext -> [Effect Set [v <> ".ph", v']]
      ([(l',_)], _) | l == l' -> []
      _ -> [i]
    renameSet _ i = [i]

    makeLoop (BB l _ is t) =
      let (g, i, s) = splitPhisBB is
          -- decide where to place the phi's and whether to split them
          placePhi (Op (Dest v t) Get []) = case setBlocks ! v of
            (_:_:_, _:_) -> ([Op (Dest (v <> ".ph") t) Get []], [Effect Set [v, v <> ".ph"]], [Op (Dest v t) Get []])
            (_, []) -> ([Op (Dest v t) Get []], [], [])
            ([(_,v')], _) -> ([], [Effect Set [v, v']], [Op (Dest v t) Get []])
            _ -> ([], [], [Op (Dest v t) Get []])
          placePhi _ = error "unreachable"
          (phG, phS, hG) = foldMap placePhi g
          l' = "header_" <> l
      in Loop (BB l [] (phG++phS) (Jmp l')) l' (BB l' [] (hG++i++s) t)
              (maybe mempty getSolo $ Map.lookup (Just l) blocks)

    mapLabels f = runIdentity . visit (defaultVisitor { visitLabel = pure . f })
    fixup (BB l _ is t) =
      let relabel l' = if (l',l) `Set.member` loops then "header_" <> l' else l'
      in BB l [] (concatMap (renameSet l) is) (mapLabels relabel t)

    blocks = Map.fromListWith (\ ~(Solo x) ~(Solo y) -> Solo (Map.union x y))
      [ (h, Solo $ Map.singleton l node)
      | (l,bb) <- Map.toList bbs
      , let h = Map.lookup l loopTreeParents
      , let node = if l `Set.member` headers then makeLoop (fixup bb) else NonLoop (fixup bb)
      ]
    Solo root = blocks ! Nothing

-- | Out of loopy form
--
-- Note that this is used internally as an alternative representation of the
-- loopy form, so it can't do extra optimizations
loopsToBBs :: Map Label LoopyNode -> Map Label BB
loopsToBBs loopy = Map.fromListWith (error "duplicates") $ goMap loopy []
  where
    goMap m rest = foldr (\(l,n) r -> goNode l n r) rest (Map.toList m)
    goNode l (Loop ph l' h m) rest = (l,ph) : (l',h) : goMap m rest
    goNode l (NonLoop b) rest = (l,b) : rest

-- | Reverse dominators
--
-- If something's not included, it's because it statically can't reach any exit
-- node.
reverseDominators :: Label -> Map Label BB -> Map Label (Set Label)
reverseDominators _ bbs = getDom <$> semiNaive initial f
  where preds = Map.fromListWith (++) [(b,[a]) | (a,b) <- edges bbs]
        initial = Map.fromList [(l,Dom $ Set.singleton l) | (l,BB _ _ _ (Ret _)) <- Map.toList bbs]
        f m diff = Map.fromList
          [ (l, Dom $ Set.insert l $ foldl1' Set.intersection [getDom (m ! p) | p <- successors (bbs ! l), Map.member p m])
          | (b,_) <- Map.toList diff, l <- fromMaybe [] $ Map.lookup b preds ]

-- | Toposort a group of instructions
scheduleInstrs :: Map Var Instr -> [Instr]
scheduleInstrs instrs = go instrs []
  where
    go m r = case Map.lookupMin m of
      Nothing -> reverse r
      Just (v,_) -> let (m',r') = goVar m v r in go m' r'
    goVar m v r = case Map.lookup v m of
      Nothing -> (m,r)
      Just i -> (i:) <$> foldl' (\(m',r') v' -> goVar m' v' r') (Map.delete v m, r) (Set.toList $ varUses i)

-- | LICM whole thing
licmOptFunction :: OptFunction -> OptFunction
licmOptFunction (OptFunction name params retTy start bbs) =
    OptFunction name params retTy start bbs'
  where loopy = buildLoopTree start bbs
        loopy' = loopInvariantCodeMotion start loopy
        bbs' = loopsToBBs loopy'

-- | LICM
loopInvariantCodeMotion :: Label -> Map Label LoopyNode -> Map Label LoopyNode
loopInvariantCodeMotion start loopy = finalResult
  where
    -- i is loop invariant if
    --  1. it's always executed when the loop is executed
    --  2. it's pure
    --  3. its arguments are loop invariant, or defined prior to the loop
    -- (1) is kinda hard: it holds if the instruction post-dominates the loop
    -- header, or in other cases too, that involve infinite loops.  I'll decide
    -- that I don't care so much about infinite loops, and conservatively
    -- approximate it using reverse dominators.

    bbs = loopsToBBs loopy
    defBlocks = definingBlocks bbs
    varToInstr = Map.fromListWith (error "duplicates")
      [(v, i) | (_,BB _ _ is _) <- Map.toList bbs, i <- is, v <- Set.toList $ varDefs i]

    -- x post-dominates y if whenever y runs, x will eventually run later
    revDoms = reverseDominators start bbs
    x `postDominates` y = case Map.lookup y revDoms of
      Nothing -> False -- Conservatively say no here, just in case
      Just ds -> x `Set.member` ds

    -- Handle (1): find the level at which it's guaranteed to execute
    minBound1 =
      let goBB !k bb rest = [(v,k) | v <- Set.toList $ varDefs bb] ++ rest
          goN !k !_ _ (NonLoop bb) = goBB k bb
          goN !k !k' l (Loop ph _ h m) = goBB k ph . goBB k h . goM k (k'+1) l m
          goM !k !k' l m rest = foldr (\(l',n) r -> goN (if l' `postDominates` l then k else k') k' l' n r) rest (Map.toList m)
      in Map.fromList $ foldr (\(l,n) r -> goN 0 0 l n r) [] (Map.toList loopy)

    -- Handle (2): we only try to lower things from this set
    pureUses = Map.fromListWith (++)
      [ (arg,[v])
      | BB l _ is _ <- toList bbs, Op (Dest v _) _ args <- is, arg <- args ]

    -- Handle (3): use dataflow to find the instructions we can execute earlier
    initialLvls :: Map Var Int
    initialLvls =
      let goBB !k bb rest = [(v,k) | v <- Set.toList $ varDefs bb] ++ rest
          goN !k (NonLoop bb) = goBB k bb
          goN !k (Loop ph _ h m) = goBB k ph . goBB (k+1) h . goM (k+1) m
          goM !k m rest = foldr (\(_,n) r -> goN k n r) rest (Map.toList m)
      in Map.fromList $ goM 0 loopy []
    initialLvl v = fromMaybe 0 (Map.lookup v initialLvls)
    loopTreeParents =
      let go _ (NonLoop _) rest = rest
          go l (Loop _ h _ m) rest =
            (h,l) : foldr (\(l',n) r -> (l',l) : go l' n r) rest (Map.toList m)
      in Map.fromList $ foldr (\(l,n) r -> go l n r) [] (Map.toList loopy)
    lcaLvl l lvl l' lvl' -- least common ancestor in the loop tree
      | lvl < lvl' = lcaLvl l lvl (loopTreeParents ! l') (lvl'-1)
      | lvl > lvl' = lcaLvl (loopTreeParents ! l) (lvl-1) l' lvl'
      | Map.lookup l loopTreeParents == Map.lookup l' loopTreeParents = lvl :: Int
      | otherwise = lcaLvl (loopTreeParents ! l) (lvl-1) (loopTreeParents ! l') (lvl'-1)
    annotatedArgs = Map.fromList
      [ (v, [(v', maybe 0 (\b -> lcaLvl l (initialLvls ! v) b (initialLvls ! v')) $ Map.lookup v' defBlocks) | v' <- args])
      | BB l _ is _ <- toList bbs, Op (Dest v _) _ args <- is ]
    computeNewLvl v m =
      let getLvl (x,lca) = min lca (fromMaybe (initialLvl x) $ getMin <$> m Map.!? x)
      in Min $ maximum ((minBound1!v) : map getLvl (annotatedArgs ! v))
    initialLvls' = Map.fromList -- make sure to check each instr at least once
      [ (v, computeNewLvl v (Min <$> initialLvls))
      | (_,BB _ _ is _) <- Map.toList bbs, Op (Dest v _) o _ <- is, o /= Get ]
    newLvls = semiNaive initialLvls' $ \m d -> Map.fromList
      [ (v', computeNewLvl v' m)
      | (v, _) <- Map.toList d, v' <- fromMaybe [] $ Map.lookup v pureUses ]
    moves = Map.map getMin $ fromMaybe Map.empty $ newLvls `without` (Min <$> initialLvls)
    -- moves is those (v,k) pairs we should be moving earlier

    -- now let's partition them by which loop's preheader they should be going into
    nthParent n l = if n == 0 then l else nthParent (n-1) (loopTreeParents ! l)
    newInstrsByLoop = Map.fromListWith Map.union
      [ (nthParent (origLvl - newLvl) (defBlocks ! v), Map.singleton v (varToInstr ! v))
      | (v,newLvl) <- Map.toList moves, let origLvl = initialLvls ! v]

    -- now let's rebuild the output
    stillNeeded (Op (Dest v _) _ _) = not $ v `Map.member` moves
    stillNeeded _ = True
    addInstrs bb@(BB l _ is t) = case Map.lookup l newInstrsByLoop of
      Nothing -> bb
      Just is' -> let (g,i,s) = splitPhisBB is in BB l [] (g++i++scheduleInstrs is'++s) t
    rebuildBB (BB l _ is t) = BB l [] (filter stillNeeded is) t
    rebuildN (NonLoop bb) = NonLoop (rebuildBB bb)
    rebuildN (Loop ph l' h m) =
      let ph' = addInstrs $ rebuildBB ph
          h' = rebuildBB h
          m' = rebuildN <$> m
      in Loop ph' l' h' m'

    finalResult = rebuildN <$> loopy


