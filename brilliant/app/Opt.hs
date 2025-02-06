-- | Some optimizations
module Opt where

import Bril
import CFG
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Functor.Identity
import Data.Functor.Const

-- | Function during optimization
--
-- All variables have been renamed to v_{original name} so that vN can be used
-- for generated names
data OptFunction =
  OptFunction
    Text -- ^ Name
    [Dest] -- ^ Parameters
    (Maybe Type) -- ^ Return type
    Label -- ^ Start label
    (Map Label BB) -- ^ All basic blocks
  deriving (Show, Eq)

instance Code OptFunction where
  visit v (OptFunction name params ret start bbs) =
    OptFunction name <$> visit v params <*> pure ret <*> visitLabel v start <*> visit v bbs

toOptFunction :: Function -> OptFunction
toOptFunction (Function name params out code) =
  let -- rename vars
      visitor = visitVars (\v -> pure ("v_" <> v))
      params' = runIdentity $ visit visitor params
      code' = runIdentity $ visit visitor code

      -- build CFG
      CFG start _ bbs = canonicalizeJumpsCFG $ buildCFG code'

  in OptFunction name params' out start bbs

-- | Re-serialize all the basic blocks.
--
-- This could be better (i.e. create a good layout for the blocks)
fromOptFunction :: OptFunction -> Function
fromOptFunction (OptFunction name params out start bbs) =
  Function name params out (Jump (Jmp start) : foldMap toCode bbs)
  where toCode (BB l ls is j) = [Label l] ++ map Label ls ++ map Instr is ++ [Jump j]

-- | Traverse basic blocks. Useful for local optimizations
traverseBBs :: Applicative f => (BB -> f BB) -> OptFunction -> f OptFunction
traverseBBs f (OptFunction name params out start bbs) =
  OptFunction name params out start <$> traverse f bbs

-- | Map basic blocks. Useful for local optimizations
mapBBs :: (BB -> BB) -> OptFunction -> OptFunction
mapBBs f = runIdentity . traverseBBs (Identity . f)

-- | Trivial dead code elimination, a local optimization.
--
-- Remove pure instructions that are either overwritten before use, are never used.
tdce :: OptFunction -> OptFunction
tdce input = mapBBs local input
  where allUsed = varUses input
        local (BB l ls is j) = BB l ls (fst (go is)) j
        go [] = ([], allUsed)
        go (i:is) = (if isPure i && not isUsed then is' else i:is', used')
          where (is', used) = go is
                isUsed = any (`Set.member` used) $ varDefs i
                used' = (used Set.\\ varDefs i) `Set.union` varUses i

varDefs :: Code a => a -> Set Var
varDefs = getConst . visit (defaultVisitor { visitDef = \(Dest v _) -> Const (Set.singleton v) })

varUses :: Code a => a -> Set Var
varUses = getConst . visit (defaultVisitor { visitUse = \v -> Const (Set.singleton v) })

