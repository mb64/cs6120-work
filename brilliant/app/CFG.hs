-- | Code to construct a control-flow graph.
--
-- Each basic block has a single canonical label, and maybe more labels too.
module CFG where

import Bril
import qualified Data.Text as T
import Data.Text (Text)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List
import Control.Monad

-- | A basic block.
--
-- Each basic block has a canonical label, some other labels, some straight-line instructions, and a terminator.
data BB = BB Label [Label] [Instr] Jump
        deriving (Show, Eq)

-- | The successors of a basic block
successors :: BB -> [Label]
successors (BB _ _ _ (Jmp l)) = [l]
successors (BB _ _ _ (Br _ l1 l2)) = [l1, l2]
successors (BB _ _ _ (Ret _)) = []

-- | The list of all edges in the CFG
edges :: Map Label BB -> [(Label,Label)]
edges bbs = [(l,s) | (l,bb) <- Map.toList bbs, s <- successors bb]

instance Code BB where
  visit v (BB l ls is j) =
    BB <$> visitLabel v l <*> traverse (visitLabel v) ls <*> visit v is <*> visit v j

-- | A control-flow graph.
--
-- The label is the (canonical) label of the entry block.
--
-- The first map canonicalizes labels. The second maps canonical labels to basic blocks.
data CFG = CFG Label (Map Label Label) (Map Label BB)
         deriving (Show, Eq)

-- | Invariant: all control-flow graphs are well-formed
wellFormedCFG :: CFG -> Either String ()
wellFormedCFG (CFG start can bbs) = do
  unless (start `Map.member` bbs) $ do
    Left "start label is bad"
  unless (and [ cl == cl' | (cl, BB cl' _ _ _) <- Map.toList bbs ]) $ do
    Left "basic block tagged incorrectly"
  unless (and [ can Map.! l == cl | (_, BB cl ls _ _) <- Map.toList bbs, l <- ls ]) $ do
    Left "labels canonicalized wrong"
  unless (and [ l `elem` (cl:ls) | (l,cl) <- Map.toList can, let BB _ ls _ _ = bbs Map.! cl ]) $ do
    Left "label map is wrong"

-- | Finalize the CFG by building the map that canonicalizes labels
basicBlocksToCFG :: Label -> [BB] -> CFG
basicBlocksToCFG start bbs = CFG start can bbsMap
  where can = Map.fromList [(l, cl) | BB cl ls _ _ <- bbs, l <- cl:ls]
        bbsMap = Map.fromList [(cl, b) | b@(BB cl _ _ _) <- bbs]

-- | Build a CFG from a list of instructions
buildCFG :: [CodeItem] -> CFG
buildCFG items = basicBlocksToCFG startLabel bbs
  where allLabels = Set.fromList [ l | Label l <- items ]
        next :: Int -> (Int, Label)
        next !n =
          let candidate = "lbl_" <> T.pack (show n) in
          if candidate `Set.member` allLabels then next (n+1) else (n+1, candidate)

        -- collect labels, then the rest of the BB
        start !n (Label l:cs) =
          let (ls, is, term, rest) = start n cs
          in (l:ls, is, term, rest)
        start !n cs =
          let (is, term, rest) = go n cs
          in ([], is, term, rest)

        -- collect the rest of the BB
        go !n [Jump j] = ([], j, [])
        go !n [] = ([], Ret Nothing, []) -- doesn't end with ret: add one
        go !n (Label l:cs) =
          let (ls, is, term, rest) = start n cs
          in ([], Jmp l, BB l ls is term : rest)
        go !n (Instr i:cs) =
          let (is, term, rest) = go n cs
          in (i:is, term, rest)
        go !n (Jump j:Label l:cs) = -- Jump followed by a label
          let (ls, is, term, rest) = start n cs
          in ([], j, BB l ls is term:rest)
        go !n (Jump j:cs) = -- Jump not followed by a label: invent a new one
          let (n', l) = next n
              (ls, is, term, rest) = start n' cs
          in ([], j, BB l ls is term:rest)

        (startLabel, bbs) =
          let (n, l, cs) = case items of
                Label l:rest -> (0, l, rest)
                _ -> let (n, l) = next 0 in (n, l, items)
              (ls, is, term, rest) = start n cs
          in (l, BB l ls is term : rest)

-- | Canonicalize jumps
canonicalizeJumpsCFG :: CFG -> CFG
canonicalizeJumpsCFG (CFG start can bbs) = CFG start can (fmap f bbs)
  where f (BB cl ls is j) = BB cl ls is (canon j)
        canon (Jmp l) = Jmp (can Map.! l)
        canon (Br x l1 l2) = Br x (can Map.! l1) (can Map.! l2)
        canon (Ret x) = Ret x


