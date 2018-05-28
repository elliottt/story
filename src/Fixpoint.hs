module Fixpoint (relevantActions) where

import Types

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Foldable as F


-- | Construct the relaxed planning graph, for satisfying the given fact from
-- the initial state.
rpg :: Graph -> Actors -> FactId -> State -> IO Actions
rpg graph actors i s =
  error "rpg"

-- | Compute relevant actions from this set of actors, target intent fact, and
-- initial world state. This corresponds to @f@ in the original paper.
relevant :: Graph -> Actors -> FactId -> State -> IO Actions
relevant graph actors i state =
  error "relevant"

-- | Return all reachable actions from the current world state, that address the
-- intent fact through actions available to the actors. This corresponds to @g@
-- in the original paper.
reachable :: Graph -> Actors -> FactId -> State -> IO Actions
reachable graph actors i state =
  error "reachable"

-- | If no actions are relevant, use the reachable actions to discover relevant
-- commands. This function corresponds to @F-COMMANDS@ in the original paper.
commands :: Graph -> Actors -> FactId -> State -> IO Actions
commands graph actors i state = loop actors
  where
  loop b =
    do r <- relevant graph b i state
       if IntSet.null r
          then do u <- reachable graph b i state
                  agents <- findAgents u
                  undefined
          else return r

  findAgents as =
    do undefined

-- | The cooperating action set for a group of actors all attempting to make the
-- given fact true. This function corresponds to @RELEVANTACTIONS-BASIC@ in the
-- original paper.
relevantActions_basic :: Graph -> State -> Intents -> IO Actions
relevantActions_basic graph state intents = go IntSet.empty (IntMap.toList intents)
  where
  go r [] =
       return r

  go r ((i,actors):rest) =
    do actions <- commands graph actors i state
       let r' = r `IntSet.union` actions
       r' `seq` go r' rest

-- | Actions that can be taken through assumptions of what others will do. This
-- corresponds to @RELEVANTACTIONS-PREDICT@ in the original paper.
relevantActions_predict :: Graph -> State -> Intents -> IO Actions
relevantActions_predict graph state intents = go IntSet.empty state
  where
  go r c =
    do t <- relevantActions_basic graph c intents 
       let c' = IntSet.unions (c : map (addEffects graph) (IntSet.toList (t IntSet.\\ r)))
           r' = r `IntSet.union` t
       c' `seq` r' `seq` go r' c'

-- | Determine relevant actions through cooperation, prediction, and delegation.
-- Filter out actions that do not apply in the initial state.
relevantActions :: Graph -> State -> Intents -> IO Actions
relevantActions graph state intents =
  do r <- relevantActions_predict graph state intents
     return (IntSet.filter (actionApplies graph state) r)
{-# INLINE relevantActions #-}
