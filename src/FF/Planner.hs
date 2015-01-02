{-# LANGUAGE RecordWildCards #-}
module FF.Planner where

import           FF.ConnGraph
import           FF.Extract ( extractPlan, helpfulActions, layer1 )
import           FF.Fixpoint
import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Control.Monad ( guard )
import           Data.Array.IO ( readArray )
import qualified Data.Foldable as F
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import           Data.List ( minimumBy )
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
enforcedHillClimbing hash cg s0 goal = loop [] (maxBound - 1) s0
  where
  loop plan h s =
    do mb <- findBetterState hash cg h s goal
       case mb of
         Just (h',s',ref) | h' == 0   -> return (Just (reverse (ref:plan)))
                          | otherwise -> loop (ref:plan) h' s'
         Nothing                      -> return Nothing

-- | Find a state whose heuristic value is strictly smaller than the current
-- state.
findBetterState :: Hash -> ConnGraph -> Int -> State -> Goals
                -> IO (Maybe (Int,State,EffectRef))
findBetterState hash cg h s goal =
  do _  <- buildFixpoint cg s goal
     mbPlan <- extractPlan cg goal
     case mbPlan of

       Just (plan,goalSet) ->
         do acts <- helpfulActions cg plan goalSet
            mb   <- successor hash cg s goal acts
            return $! do res@(h',_,_) <- mb
                         guard (h' > h)
                         return res

       -- no plan
       Nothing ->
         return Nothing

-- | Apply effects to the current state, returning the minimal next choice (if
-- it exists).
successor :: Hash -> ConnGraph -> State -> Goals
          -> [EffectRef]
          -> IO (Maybe (Int,State,EffectRef))
successor hash cg s goal refs =
  do mbs <- mapM heuristic refs
     case catMaybes mbs of
       [] -> return Nothing
       hs -> return $! Just $! minimumBy (comparing fst3) hs

  where

  fst3 (a,_,_) = a

  heuristic ref =
    do s'  <- applyEffect cg ref s
       mbH <- computeHeuristic hash cg s' goal
       return $ do h' <- mbH
                   return (h',s',ref)

-- | Apply an effect to the state given, returning a new state.
applyEffect :: ConnGraph -> EffectRef -> State -> IO State
applyEffect cg ref s =
  do Effect { .. } <- readArray (cgEffects cg) ref
     return $! (s `RS.union` eAdds) RS.\\ eDels

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


-- Greedy Best-first Search ----------------------------------------------------

greedyBestFirst :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Steps)
greedyBestFirst hash cg s0 goal = loop Seq.empty s0 maxBound
  where

  -- when the heuristic value hits zero, the goals have been achieved
  loop effs _ 0 =
       return (Just (F.toList effs))

  loop effs s h =
    do _      <- buildFixpoint cg s goal
       mbPlan <- extractPlan cg goal
       case mbPlan of

         -- found a plan, compute the heuristic for each action in the first
         -- layer
         Just (plan,_) ->
           do mb <- successor hash cg s goal =<< layer1 cg plan
              case mb of
                Just (h',s',ref) -> loop (effs Seq.|> ref) s' (min h h')
                Nothing          -> return Nothing

         -- can't find a path to the goal from here
         Nothing ->
              return Nothing


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
