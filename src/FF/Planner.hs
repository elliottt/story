{-# LANGUAGE RecordWildCards #-}
module FF.Planner where

import           FF.ConnGraph
import           FF.Extract
import           FF.Fixpoint
import qualified FF.RefSet as RS

import           Control.Monad ( guard )
import           Data.Array.IO ( readArray )
import           Data.Maybe ( isJust )
import qualified Data.IntMap.Strict as IM


type Plan = [EffectRef]

--findPlan :: I.Domain -> I.Problem -> IO (Maybe Plan)
findPlan dom plan =
  do (s0,goal,cg) <- buildConnGraph dom plan
     mb <- enforcedHillClimbing cg s0 goal
     if isJust mb
        then return mb
        else greedyBestFirst cg s0 goal

enforcedHillClimbing :: ConnGraph -> State -> Goals -> IO (Maybe Plan)
enforcedHillClimbing cg s0 goal = loop [] (maxBound - 1) s0
  where
  loop plan h s =
    do mb <- findBetterState cg h s goal
       case mb of
         Just (h',s',ref) | h' == 0   -> return (Just (reverse (ref:plan)))
                          | otherwise -> loop (ref:plan) h' s'
         Nothing                      -> return Nothing

-- | Find a state whose heuristic value is strictly smaller than the current
-- state.  NOTE: this would very much benefit from the state caching that the C
-- implementation of fast-forward does.
findBetterState :: ConnGraph -> Int -> State -> Goals
                -> IO (Maybe (Int,State,EffectRef))
findBetterState cg h s goal =
  do _  <- buildFixpoint cg s goal
     mb <- extractPlan cg goal
     case mb of

       Just (plan,goalSet) ->
         do acts <- helpfulActions cg plan goalSet
            print acts
            case acts of
              []  -> return Nothing

              [ref] -> do Effect { .. } <- readArray (cgEffects cg) ref
                          let s' = (s `RS.union` eAdds) RS.\\ eDels
                          mbH <- computeHeuristic cg s' goal
                          print ("H", mbH)
                          return $ do h' <- mbH
                                      guard (h' < h)
                                      return (h',s',ref)

              -- find the best option
              as  -> error "multiple options"

       -- no plan
       Nothing ->
         return Nothing

computeHeuristic :: ConnGraph -> State -> Goals -> IO (Maybe Int)
computeHeuristic cg s goal =
  do _  <- buildFixpoint cg s goal
     mb <- extractPlan cg goal
     return $ do (plan,_) <- mb
                 return (length plan)

greedyBestFirst :: ConnGraph -> State -> Goals -> IO (Maybe Plan)
greedyBestFirst cg s0 goals = error "greedy best-first"
