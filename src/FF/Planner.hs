{-# LANGUAGE RecordWildCards #-}
module FF.Planner where

import           FF.ConnGraph
import           FF.Extract
import           FF.Fixpoint
import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Control.Monad ( guard )
import           Data.Array.IO ( readArray )
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.List ( minimumBy )
import           Data.Maybe ( isJust, fromMaybe, catMaybes )
import           Data.Ord ( comparing )
import qualified Data.Sequence as Seq


type Plan = [EffectRef]

findPlan :: I.Domain -> I.Problem -> IO (Maybe Plan)
findPlan dom plan =
  do (s0,goal,cg) <- buildConnGraph dom plan
     hash         <- newHash
     mb <- enforcedHillClimbing hash cg s0 goal
     if isJust mb
        then return mb
        else greedyBestFirst cg s0 goal

enforcedHillClimbing :: Hash -> ConnGraph -> State -> Goals -> IO (Maybe Plan)
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
     mb <- extractPlan cg goal
     case mb of

       Just (plan,goalSet) ->
         do acts <- helpfulActions cg plan goalSet
            case acts of
              []  -> return Nothing

              [ref] -> do mb <- lookupHeuristic ref
                          case mb of
                            Just res@(h',_,_) | h' < h -> return mb
                            _                          -> return Nothing

              -- find the best option
              as -> do mbs <- mapM lookupHeuristic as
                       let fst3 (a,_,_) = a
                           res@(h',_,_) = minimumBy (comparing fst3)
                                              (catMaybes mbs)
                       return $ do guard (h' < h)
                                   return res

       -- no plan
       Nothing ->
         return Nothing

  where

  -- compute the heuristic value for the state that results after applying the
  -- given effect, and hash it.
  lookupHeuristic ref =
    do Effect { .. } <- readArray (cgEffects cg) ref
       let s' = (s `RS.union` eAdds) RS.\\ eDels
       mb <- lookupState hash s'
       case mb of
         Just h  -> return (Just (h, s', ref))
         Nothing -> do mbH <- computeHeuristic cg s' goal
                       hashState hash s' (fromMaybe maxBound mbH)
                       return $ do h <- mbH
                                   return (h, s', ref)

-- | Compute the size of the relaxed plan produced by the given starting state
-- and goals.
computeHeuristic :: ConnGraph -> State -> Goals -> IO (Maybe Int)
computeHeuristic cg s goal =
  do _  <- buildFixpoint cg s goal
     mb <- extractPlan cg goal
     return $ do (plan,_) <- mb
                 return (length plan)

greedyBestFirst :: ConnGraph -> State -> Goals -> IO (Maybe Plan)
greedyBestFirst cg s0 goals = error "greedy best-first"


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
