module FF.Planner where

import           FF.ConnGraph
import           FF.Extract
import           FF.Fixpoint

import           Data.Array.IO ( readArray )
import           Data.Maybe ( isJust )
import qualified Data.IntMap.Strict as IM


type Plan = [Effect]

--findPlan :: I.Domain -> I.Problem -> IO (Maybe Plan)
findPlan dom plan =
  do (s0,goal,cg) <- buildConnGraph dom plan
     mb <- enforcedHillClimbing cg s0 goal
     if isJust mb
        then return mb
        else greedyBestFirst cg s0 goal

enforcedHillClimbing :: ConnGraph -> State -> Goals -> IO (Maybe Plan)
enforcedHillClimbing cg s0 goal = loop s0
  where
  loop s =
    do _  <- buildFixpoint cg s goal
       mb <- extractPlan cg goal
       case mb of
         Just (plan,gs) ->
           do print =<< helpfulActions cg plan gs
              print (gs IM.! 2) -- G_1
              print plan
              printFacts cg
              printEffects cg

         Nothing ->
              return ()

       undefined

greedyBestFirst :: ConnGraph -> State -> Goals -> IO (Maybe Plan)
greedyBestFirst cg s0 goals = undefined
