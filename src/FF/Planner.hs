{-# LANGUAGE RecordWildCards #-}
module FF.Planner where

import           FF.ConnGraph
import           FF.Extract ( extractPlan, allActions, helpfulActions )
import           FF.Fixpoint
import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Control.Monad ( unless )
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.List ( sortBy, insertBy )
import           Data.Maybe ( isJust, fromMaybe, catMaybes )
import           Data.Ord ( comparing )
import qualified Data.Text as T


type Plan = [T.Text]

findPlan :: I.Domain -> I.Problem -> IO (Maybe Plan)
findPlan dom plan =
  do (s0,goal,cg) <- buildConnGraph dom plan
     hash         <- newHash
     mbRoot       <- rootNode cg s0 goal
     case mbRoot of
       Nothing   -> return Nothing
       Just root ->
         do mb <- enforcedHillClimbing hash cg root goal
            mkPlan cg =<< if isJust mb
                             then return mb
                             else greedyBestFirst hash cg root goal
  where
  mkPlan cg (Just effs) = Just `fmap` mapM (getOper cg) effs
  mkPlan _  Nothing     = return Nothing

  getOper cg eref =
    do Effect { .. } <- getNode cg eref
       Oper { .. }   <- getNode cg eOp
       return oName


-- Enforced Hill Climbing ------------------------------------------------------

type Steps = [EffectRef]

enforcedHillClimbing :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Steps)
enforcedHillClimbing hash cg root goal =
  loop root

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
  do let Heuristic { .. } = nodeHeuristic n
     acts  <- helpfulActions cg hActions hGoals
     succs <- successors hash cg n goal acts
     case succs of
       n' : _ | nodeMeasure n' < nodeMeasure n -> return (Just n')
       _                                       -> return Nothing


-- Greedy Best-first Search ----------------------------------------------------

greedyBestFirst :: Hash -> ConnGraph -> Node -> Goals -> IO (Maybe Steps)
greedyBestFirst hash cg root goal =
  go HS.empty [root { nodeHeuristic = (nodeHeuristic root) { hMeasure = maxBound }}]

  where

  go seen (n @ Node { .. } :rest)
    | nodeMeasure n == 0 =
         return (Just (extractPath n))

      -- don't generate children for nodes that have already been visited
    | nodeState `HS.member` seen =
         go seen rest

    | otherwise =
      do children <- successors hash cg n goal (RS.toList (hActions nodeHeuristic))
         go (HS.insert nodeState seen) (foldr insertChild rest children)

  go _ [] = return Nothing

  insertChild = insertBy (comparing aStarMeasure)


-- Utilities -------------------------------------------------------------------

-- | Search nodes.
data Node = Node { nodeState :: State
                   -- ^ The state after the effect was applied
                 , nodePathMeasure :: !Int
                   -- ^ The cost of this path
                 , nodeParent :: Maybe (Node,EffectRef)
                   -- ^ The state before this one in the plan, and the effect
                   -- that caused the difference
                 , nodeHeuristic :: !Heuristic
                   -- ^ The actions applied in the first and second layers of
                   -- the relaxed graph for this node.
                 } deriving (Show)

rootNode :: ConnGraph -> State -> Goals -> IO (Maybe Node)
rootNode cg nodeState goal =
  do mbH <- measureState cg nodeState goal
     case mbH of
       Just nodeHeuristic ->
            return $ Just Node { nodeParent      = Nothing
                               , nodePathMeasure = 0
                               , ..
                               }

       Nothing ->
            return Nothing

childNode :: Node -> State -> EffectRef -> Heuristic -> Node
childNode parent nodeState ref nodeHeuristic =
  Node { nodeParent      = Just (parent,ref)
       , nodePathMeasure = nodePathMeasure parent + 1
       , ..
       }

aStarMeasure :: Node -> Int
aStarMeasure n = nodePathMeasure n + nodeMeasure n

-- | The distance that this node is from the goal state.
nodeMeasure :: Node -> Int
nodeMeasure Node { nodeHeuristic = Heuristic { .. } } = hMeasure

-- | Extract the set of effects applied to get to this state.  This ignores the
-- root node, as it represents the initial state.
extractPath :: Node -> [EffectRef]
extractPath  = go []
  where
  go plan Node { .. } =
    case nodeParent of
      Just (p,op) -> go (op : plan) p
      Nothing     -> plan


-- | Apply effects to the current state, returning the valid choices ordered by
-- their heuristic value.
successors :: Hash -> ConnGraph -> Node -> Goals -> [EffectRef] -> IO [Node]
successors hash cg parent goal refs =
  do mbs <- mapM heuristic refs
     return $! sortBy (comparing nodeMeasure) (catMaybes mbs)

  where

  heuristic nodeOp =
    do nodeState <- applyEffect cg nodeOp (nodeState parent)
       mbH       <- computeHeuristic hash cg nodeState goal
       return $ do h <- mbH
                   return (childNode parent nodeState nodeOp h)


data Heuristic = Heuristic { hMeasure :: !Int
                             -- ^ The heuristic value for this state.
                           , hActions :: Effects
                             -- ^ All actions from the first layer of the
                             -- relaxed planning graph
                           , hGoals   :: Goals
                             -- ^ The goals generated by layer 1 of the relaxed
                             -- planning graph
                           } deriving (Show)

-- | The Heuristic value that suggests no action.
badHeuristic :: Heuristic
badHeuristic  = Heuristic { hMeasure = maxBound
                          , hActions = RS.empty
                          , hGoals   = RS.empty
                          }

-- compute the heuristic value for the state that results after applying the
-- given effect, and hash it.
computeHeuristic :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Heuristic)
computeHeuristic hash cg s goal =
  do mb <- lookupState hash s
     case mb of
       -- return the cached heuristic
       Just h' ->    return (Just h')

       -- compute and cache the heuristic
       Nothing -> do mbH <- measureState cg s goal
                     hashState hash s (fromMaybe badHeuristic mbH)
                     return mbH

-- | Compute the size of the relaxed plan produced by the given starting state
-- and goals.
measureState :: ConnGraph -> State -> Goals -> IO (Maybe Heuristic)
measureState cg s goal =
  do _        <- buildFixpoint cg s goal
     mb       <- extractPlan cg goal
     hActions <- allActions cg s
     return $! do (hMeasure,gs) <- mb
                  let hGoals = fromMaybe RS.empty (IM.lookup 1 gs)
                  return Heuristic { .. }


-- State Hashing ---------------------------------------------------------------

data Hash = Hash { shHash :: !(IORef (HM.HashMap State Heuristic))
                 }

newHash :: IO Hash
newHash  =
  do shHash <- newIORef HM.empty
     return Hash { .. }

-- | Add a new entry in the hash for a state.
hashState :: Hash -> State -> Heuristic -> IO ()
hashState h s val =
  do mb <- lookupState h s
     unless (isJust mb) $
       do states <- readIORef (shHash h)
          writeIORef (shHash h) $! HM.insert s val states

lookupState :: Hash -> State -> IO (Maybe Heuristic)
lookupState Hash { .. } s =
  do states <- readIORef shHash
     return $! HM.lookup s states
