{-# LANGUAGE RecordWildCards #-}
module FF.Planner where

import           FF.ConnGraph
import           FF.Extract ( extractPlan, helpfulActions, getActions )
import           FF.Fixpoint
import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Data.Array.IO ( readArray )
import qualified Data.HashSet as HS
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import           Data.List ( sortBy, insertBy )
import           Data.Maybe ( isJust, fromMaybe, catMaybes )
import           Data.Ord ( comparing )
import qualified Data.Sequence as Seq
import qualified Data.Text as T


type Plan = [T.Text]

findPlan :: I.Domain -> I.Problem -> IO (Maybe Plan)
findPlan dom plan =
  do (s0,goal,cg) <- buildConnGraph dom plan
     hash         <- newHash
     mb <- enforcedHillClimbing hash cg s0 goal
     mkPlan cg =<< if isJust mb
                      then return mb
                      else greedyBestFirst hash cg s0 goal
  where
  mkPlan cg (Just effs) = Just `fmap` mapM (getOper cg) effs
  mkPlan _  Nothing     = return Nothing

  getOper cg eref =
    do Effect { .. } <- readArray (cgEffects cg) eref
       Oper { .. }   <- readArray (cgOpers cg) eOp
       return oName


-- Enforced Hill Climbing ------------------------------------------------------

type Steps = [EffectRef]

enforcedHillClimbing :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Steps)
enforcedHillClimbing hash cg s0 goal = loop (initialNode s0)
  where

  loop n =
    do mb <- findBetterState hash cg n goal
       case mb of

         Just n'
           | nodeMeasure n' == 0 -> return (Just (extractPath n'))
           | otherwise           -> loop n'

         Nothing -> return Nothing

-- | Find a state whose heuristic value is strictly smaller than the current
-- state.
findBetterState :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Node)
findBetterState hash cg n goal =
  do _     <- buildFixpoint cg (nodeState n) goal
     acts  <- helpfulActions cg (nodeState n)
     succs <- successors hash cg n goal acts
     case succs of
       n' : _ | nodeMeasure n' < nodeMeasure n -> return (Just n')
       _                                       -> return Nothing


-- Greedy Best-first Search ----------------------------------------------------

greedyBestFirst :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Steps)
greedyBestFirst hash cg s0 goal = go HS.empty [initialNode s0]
  where

  go seen (n @ Node { .. } :rest)
    | nodeMeasure == 0 =
         return (Just (extractPath n))

      -- don't generate children for nodes that have already been visited
    | nodeState `HS.member` seen =
         go seen rest

    | otherwise =
      do _        <- buildFixpoint cg nodeState goal
         (effs,_) <- getActions cg nodeState
         children <- successors hash cg n goal (RS.toList effs)
         go (HS.insert nodeState seen) (foldr insertChild rest children)

  go _ [] = return Nothing

  insertChild = insertBy (comparing nodeMeasure)


-- Utilities -------------------------------------------------------------------

-- | Search nodes.
data Node = Node { nodeState :: State
                   -- ^ The state after the effect was applied
                 , nodeOp :: EffectRef
                   -- ^ The effect applied to arrive at this state
                 , nodeMeasure :: !Int
                   -- ^ The heuristic value of this node
                 , nodeParent :: Maybe Node
                   -- ^ The state before this one in the plan
                 } deriving (Show)

initialNode :: State -> Node
initialNode nodeState = Node { nodeParent  = Nothing
                             , nodeOp      = EffectRef (-1)
                             , nodeMeasure = maxBound
                             , ..
                             }

-- | Extract the set of effects applied to get to this state.  This ignores the
-- root node, as it represents the initial state.
extractPath :: Node -> [EffectRef]
extractPath  = go []
  where
  go plan Node { .. } =
    case nodeParent of
      Just p  -> go (nodeOp : plan) p
      Nothing -> plan


-- | Apply effects to the current state, returning the valid choices ordered by
-- their heuristic value.
successors :: Hash -> ConnGraph -> Node -> Goals -> [EffectRef] -> IO [Node]
successors hash cg parent goal refs =
  do mbs <- mapM heuristic refs
     return $! sortBy (comparing nodeMeasure) (catMaybes mbs)

  where

  nodeParent = Just parent

  heuristic nodeOp =
    do nodeState <- applyEffect cg nodeOp (nodeState parent)
       mbH       <- computeHeuristic hash cg nodeState goal
       return $ do nodeMeasure <- mbH
                   return Node { .. }

-- compute the heuristic value for the state that results after applying the
-- given effect, and hash it.
computeHeuristic :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Int)
computeHeuristic hash cg s goal =
  do mb <- lookupState hash s
     case mb of
       -- return the cached heuristic
       Just h' ->    return (Just h')

       -- compute and cache the heuristic
       Nothing -> do mbH <- heuristic
                     hashState hash s (fromMaybe maxBound mbH)
                     return mbH
  where

  -- Compute the size of the relaxed plan produced by the given starting state
  -- and goals.
  heuristic =
    do _  <- buildFixpoint cg s goal
       mb <- extractPlan cg goal
       return $ do (plan,_) <- mb
                   return (length plan)


-- State Hashing ---------------------------------------------------------------

data Hash = Hash { shHash :: !(IORef (Seq.Seq HashedState))
                 }

data HashedState = HashedState { hsState :: State
                               , hsSum   :: !Int
                                 -- ^ The heuristic value for this state.
                               } deriving (Show)

newHash :: IO Hash
newHash  =
  do shHash <- newIORef Seq.empty
     return Hash { .. }

-- | Add a new entry in the hash for a state.
hashState :: Hash -> State -> Int -> IO ()
hashState h s hsSum =
  do mb <- lookupState h s
     case mb of
       Nothing -> do states <- readIORef (shHash h)
                     writeIORef (shHash h)
                         (HashedState { hsState = s, .. } Seq.<| states)
       Just {} -> return ()

lookupState :: Hash -> State -> IO (Maybe Int)
lookupState Hash { .. } s =
  do states <- readIORef shHash
     case Seq.viewl (Seq.dropWhileL notState states) of
       HashedState { .. } Seq.:< _ -> return (Just hsSum)
       Seq.EmptyL                  -> return Nothing
  where
  notState HashedState { .. } = s /= hsState
