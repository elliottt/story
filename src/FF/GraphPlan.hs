{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module FF.GraphPlan where

import           Control.Monad ( guard, mzero )
import           Data.Array
import           Data.List ( foldl' )
import qualified Data.IntSet as IS


-- Facts -----------------------------------------------------------------------

-- | A reference to a fact, stored in the facts layer.
newtype FactRef = FactRef Int
                  deriving (Ix,Eq,Ord,Show,Num,Enum)

data Fact = Fact { fPred :: Pred
                   -- ^ The actual fact
                 , fActions :: [ActionRef]
                   -- ^ Actions that are related to this fact
                 } deriving (Show)

data Pred = Pred
            deriving (Show)

newtype Facts = Facts (Array FactRef Fact)
                deriving (Show)


-- Actions ---------------------------------------------------------------------

newtype ActionRef = ActionRef Int
                    deriving (Ix,Eq,Ord,Show,Num,Enum)

data Action = Action { aPre :: IS.IntSet
                       -- ^ All the facts that this action depends on
                     , aEffects :: [Effect]
                       -- ^ The (conditional) effects of this action
                     } deriving (Show)

data Effect = Effect { ePre
                       -- ^ Conditions for this effect
                     , eAdd
                       -- ^ Additions
                     , eDel :: IS.IntSet
                       -- ^ Deletions
                     } deriving (Show)

newtype Actions = Actions (Array ActionRef Action)


-- States ----------------------------------------------------------------------

class IsState state where

  -- | Whether or not one state entails another.
  entails :: state -> state -> Bool

  -- | Add an action to a state, assuming that its preconditions are satisfied
  -- by the state.
  addAction :: state -> Action -> state

addActions :: IsState state => state -> [Action] -> state
addActions  = foldl' addAction


-- | States are just sets of facts.
newtype State = State IS.IntSet
                deriving (Show)

instance IsState State where

  entails (State a) (State b) = b `IS.isSubsetOf` a

  addAction (State s0) Action { .. } = State (foldl' update s0 aEffects)
    where
    update s Effect { .. }
      | IS.null ePre || IS.isSubsetOf ePre s0 = (s `IS.union` eAdd) IS.\\ eDel

      | otherwise = s



-- | Relaxed states are ones where new actions never act on their delete
-- effects.
newtype Relaxed = Relaxed IS.IntSet
                  deriving (Show)

relax :: State -> Relaxed
relax (State s) = Relaxed s

instance IsState Relaxed where

  entails (Relaxed a) (Relaxed b) = b `IS.isSubsetOf` a

  addAction (Relaxed s0) Action { .. } = Relaxed (foldl' update s0 aEffects)
    where
    update s Effect { .. }
      | IS.null ePre || IS.isSubsetOf ePre s0 = s `IS.union` eAdd
      | otherwise                             = s


-- Relaxed Planning Graphs -----------------------------------------------------

-- | Relaxed planning graphs.
data Graph = Initial !Relaxed
           | Apply Graph      -- Previous state
                   !IS.IntSet -- Actions applied
                   !Relaxed   -- New state
             deriving (Show)

-- | The current state of the graph.
graphState :: Graph -> Relaxed
graphState (Apply _ _ s) = s
graphState (Initial s)   = s

-- | The FF heuristic.
h_ff :: Graph -> Int
h_ff  = go 0
  where
  go n (Apply g as _) = (go $! n + IS.size as) g
  go n (Initial _)    = n


-- Relaxed Planning ------------------------------------------------------------

-- | Levels of applicable actions.
type RelaxedPlan = [[ActionRef]]

-- | Given a maximum depth, a starting state and a goal state, return a relaxed
-- plan.
relaxedPlan :: Facts -> Actions -> Int -> Relaxed -> Relaxed -> Maybe RelaxedPlan
relaxedPlan facts acts maxDepth initial goal =
  do graph <- relaxedGraph facts acts maxDepth initial goal
     return (findPlan graph)


relaxedGraph :: Facts -> Actions -> Int -> Relaxed -> Relaxed -> Maybe Graph
relaxedGraph facts acts maxDepth initial goal = go 0 (Initial initial)
  where

  go n g
    | s `entails` goal =
         return g

    | n < maxDepth =
      do let (refs,as) = applicableActions facts acts s
         guard (not (IS.null refs))
         go (n+1) (Apply g refs (addActions s as))

    | otherwise =
         mzero

    where

    s = graphState g


-- XXX this should cache the resulting set of actions, as it's likely that
-- search will pass through states multiple times when looking for the same
-- goal.
applicableActions :: Facts -> Actions -> Relaxed -> (IS.IntSet,[Action])
applicableActions (Facts facts) (Actions acts) (Relaxed s) =
  foldl' step (IS.empty, []) actions

  where

  -- filter down the actions by ones that have at least some overlap with the
  -- current state
  actions = [ (aref,acts ! aref) | ref         <- IS.toList s
                                 , let Fact { .. } = facts ! FactRef ref
                                 , aref        <- fActions ]


  step (refs,as) (ActionRef ref,act)
    | ref `IS.member` refs                   = (refs,as)
    | Relaxed s `entails` Relaxed (aPre act) = (IS.insert ref refs, act:as)
    | otherwise                              = (refs,as)


-- | Work backwards through the plan, gathering steps that are required in the
-- relaxed plan.
findPlan :: Graph -> RelaxedPlan
findPlan graph = undefined
