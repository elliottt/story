{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module FF.Extract where

import           FF.ConnGraph
import qualified FF.RefSet as RS

import           Control.Monad ( foldM )
import           Data.Array.IO ( readArray )
import           Data.IORef ( readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.Monoid ( mappend )


type GoalSet = IM.IntMap Goals

goalSet :: ConnGraph -> Goals -> IO (Level,GoalSet)
goalSet ConnGraph { .. } goals = go 1 IM.empty (RS.toList goals)
  where
  go !m !gs (g:rest) =
    do Fact { .. } <- readArray cgFacts g
       i <- readIORef fLevel
       go (max m i) (IM.insertWith mappend i (RS.singleton g) gs) rest

  go !m !gs [] =
       return (m,gs)


difficulty :: ConnGraph -> EffectRef -> IO Level
difficulty ConnGraph { .. } e =
  do Effect { .. } <- readArray cgEffects e
     go maxBound (RS.toList ePre)
  where
  go !l (f:fs) =
    do Fact { .. } <- readArray cgFacts f
       i <- readIORef fLevel
       go (min l i) fs

  go l [] =
       return l

type RelaxedPlan = [EffectRef]

-- | Extract a plan from a fixed connection graph.
extractPlan :: ConnGraph -> Goals -> IO RelaxedPlan
extractPlan cg @ ConnGraph { .. } goals0 =
  do (m,gs) <- goalSet cg goals0
     solveGoals [] m gs
  where

  -- solve goals that are added at this fact level.
  solveGoals plan factLevel gs
    | factLevel > 0 =
      do (plan',gs') <-
           case IM.lookup factLevel gs of
             Just goals -> foldM (solveGoal factLevel) (plan,gs) (RS.toList goals)
             Nothing    -> return (plan,gs)

         solveGoals plan' (factLevel - 2) gs'

    | otherwise =
         return plan

  solveGoal factLevel acc@(plan,gs) g =
    do Fact { .. } <- readArray cgFacts g

       -- the goal was solved by something else at this level
       isTrue <- readIORef fIsTrue
       if isTrue == factLevel
          then return acc
          else do e <- pickBest (RS.toList fAdd)
                  Effect { .. } <- readArray cgEffects e
                  gs' <- filterGoals gs factLevel (RS.toList ePre)
                  mapM_ (markAdd factLevel) (RS.toList eAdds)
                  return (e:plan,gs')

  filterGoals gs factLevel (f:fs) =
    do Fact { .. } <- readArray cgFacts f

       isGoal <- readIORef fIsGoal
       isTrue <- readIORef fIsTrue

       -- (isTrue /= factLevel) the goal was not solved by something else at
       --                       this level
       -- not isGoal            the goal hasn't already been added by something
       --                       else
       if isTrue /= factLevel && not isGoal
          then
            do writeIORef fIsGoal True

               l <- readIORef fLevel
               filterGoals (IM.insertWith mappend l (RS.singleton f) gs)
                           factLevel fs

          else filterGoals gs factLevel fs

  filterGoals gs _ _ = return gs


  -- mark the fact as being added at i
  markAdd i f =
    do Fact { .. } <- readArray cgFacts f
       writeIORef fIsTrue i


  -- pick the best effect that achieves this goal, using the difficulty
  -- heuristic
  pickBest [] = fail "extractPlan: invalid connection graph"
  pickBest es = snd `fmap` foldM check (maxBound,undefined) es
    where
    check (d,e) r =
      do d' <- difficulty cg r
         let acc | d' < d    = (d',r)
                 | otherwise = (d,e)
         return $! acc
