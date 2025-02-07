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
import Control.Monad.State

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
tdce, tdceOnePass :: OptFunction -> OptFunction
tdce = iterToFixpoint tdceOnePass
tdceOnePass input = mapBBs local input
  where allUsed = varUses input
        local (BB l ls is j) = BB l ls (fst (go is)) j
        go [] = ([], allUsed)
        go (i:is) = (if isPure i && not isUsed then is' else i:is', used')
          where (is', used) = go is
                isUsed = any (`Set.member` used) $ varDefs i
                used' = (used Set.\\ varDefs i) `Set.union` varUses i

-- | Iterate to convergence. A bad idea in practice
iterToFixpoint :: Eq a => (a -> a) -> (a -> a)
iterToFixpoint f = go
  where go x = if x == f x then x else go (f x)

visitUses :: (Applicative f, Code a) => (Var -> f Var) -> a -> f a
visitUses f = visit (defaultVisitor { visitUse = f })

mapUses :: Code a => (Var -> Var) -> a -> a
mapUses f = runIdentity . visitUses (Identity . f)

visitDefs :: (Applicative f, Code a) => (Dest -> f Dest) -> a -> f a
visitDefs f = visit (defaultVisitor { visitDef = f })

varDefs :: Code a => a -> Set Var
varDefs = getConst . visitDefs (\(Dest v _) -> Const (Set.singleton v))

varUses :: Code a => a -> Set Var
varUses = getConst . visitUses (\v -> Const (Set.singleton v))


-- | Local value numbering
--
lvn :: OptFunction -> OptFunction
lvn input = mapBBs lvnOneBasicBlock input

data LvnValue = LvnConst Lit | LvnOp Op [Either Var Int] | LvnCall Int deriving (Show, Eq, Ord)

lvnOneBasicBlock :: BB -> BB
lvnOneBasicBlock (BB l ls is j) =
    let (is', j') = go mempty mempty mempty is
    in BB l ls is' j'
  where varNameFor n = "lvn_" <> l <> "_" <> T.pack (show n)

        mapVar env idToHome v = case Map.lookup v env of
          Just i -> idToHome Map.! i
          Nothing -> v

        varToId env v = case Map.lookup v env of
          Just i -> Right i
          Nothing -> Left v

        maybeWrite d@(Dest v _) val env valToId idToHome insts =
          case Map.lookup val valToId of
            Just i -> -- Already computed!
              (Map.insert v i env, valToId, idToHome, [Op d Id [idToHome Map.! i]])
            Nothing -> (++insts) <$> write d val env valToId idToHome

        write d@(Dest v t) val env valToId idToHome =
          let newId = Map.size idToHome
              env' = Map.insert v newId env
              valToId' = Map.insert val newId valToId
              idToHome' = Map.insert newId v idToHome
          in case Map.lookup v env of
              Just oldId -> -- there was already a var there :( move it elsewhere
                let vOld = varNameFor oldId
                    idToHome'' = Map.insert oldId vOld idToHome'
                in (env', valToId', idToHome'', [Op (Dest vOld t) Id [v]])
              Nothing -> (env', valToId', idToHome', [])

        -- env
        -- map from number to canonical home
        -- map from value to number
        go env valToId idToHome [] =
          ([], mapUses (mapVar env idToHome) j)
        go env valToId idToHome (Constant d x:is) =
          let (env', valToId', idToHome', writeIs) = maybeWrite d (LvnConst x) env valToId idToHome [Constant d x]
              (rest, j') = go env' valToId' idToHome' is
          in (writeIs ++ rest, j')
        go env valToId idToHome (Op d op args:is) =
          let args' = map (mapVar env idToHome) args
              args'' = map (varToId env) args
              (env', valToId', idToHome', writeIs) = maybeWrite d (LvnOp op args'') env valToId idToHome [Op d op args']
              (rest, j') = go env' valToId' idToHome' is
          in (writeIs ++ rest, j')
        go env valToId idToHome (Call (Just d) f args:is) =
          let args' = map (mapVar env idToHome) args
              i = Map.size idToHome
              (env', valToId', idToHome', writeIs) = write d (LvnCall i) env valToId idToHome
              (rest, j') = go env' valToId' idToHome' is
          in (writeIs ++ [Call (Just d) f args'] ++ rest, j')
        go env valToId idToHome (Call Nothing f args:is) =
          let args' = map (mapVar env idToHome) args
              (rest, j') = go env valToId idToHome is
          in (Call Nothing f args' : rest, j')
        go env valToId idToHome (Effect op args:is) =
          let args' = map (mapVar env idToHome) args
              (rest, j') = go env valToId idToHome is
          in (Effect op args' : rest, j')



