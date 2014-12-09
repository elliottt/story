{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiWayIf #-}

module FF.Extract where

import           FF.ConnGraph
import qualified FF.RefSet as RS

import           Control.Monad ( foldM, filterM )
import           Data.Array.IO ( readArray )
import           Data.IORef ( readIORef, writeIORef )
import qualified Data.IntMap.Strict as IM
import           Data.Monoid ( mappend )


-- | A map from fact level to the goals that appear there.
type GoalSet = IM.IntMap Goals

-- | Construct the initial goal set for a set of presumed solved goals in the
-- connection graph.  If the goals have not been solved, the level returned will
-- be maxBound.
--
-- NOTE: in fast-forward, when a goal with level INFINITY is encountered, this
-- process returns immediately the value INFINITY, and doesn't complete the goal
-- set.
goalSet :: ConnGraph -> Goals -> IO (Maybe (Level,GoalSet))
goalSet ConnGraph { .. } goals = go 1 IM.empty (RS.toList goals)
  where
  go !m !gs (g:rest) =
    do Fact { .. } <- readArray cgFacts g
       i <- readIORef fLevel

       if i == maxBound
          then return Nothing
          else do writeIORef fIsGoal True
                  go (max m i) (IM.insertWith mappend i (RS.singleton g) gs) rest

  go !m !gs [] = return (Just (m,gs))


-- | The difficulty heuristic for an effect: the lowest level where one of the
-- effect's preconditions appears.
difficulty :: ConnGraph -> EffectRef -> IO Level
difficulty ConnGraph { .. } e =
  do Effect { .. } <- readArray cgEffects e
     foldM minPrecondLevel maxBound (RS.toList ePre)
  where
  minPrecondLevel l ref =
    do Fact { .. } <- readArray cgFacts ref
       l' <- readIORef fLevel
       return $! min l l'

type RelaxedPlan = [EffectRef]

-- | Extract a plan from a fixed connection graph.
extractPlan :: ConnGraph -> Goals -> IO (Maybe (RelaxedPlan,GoalSet))
extractPlan cg @ ConnGraph { .. } goals0 =
  do mb <- goalSet cg goals0
     case mb of
       Just (m,gs) -> solveGoals [] m gs
       Nothing     -> return Nothing
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
         return (Just (plan,gs))

  solveGoal factLevel acc@(plan,gs) g =
    do Fact { .. } <- readArray cgFacts g

       -- the goal was solved by something else at this level
       isTrue <- readIORef fIsTrue
       if isTrue == factLevel
          then return acc
          else do e <- pickBest (factLevel - 1) (RS.toList fAdd)
                  Effect { .. } <- readArray cgEffects e
                  gs' <- foldM (filterGoals factLevel) gs (RS.toList ePre)
                  mapM_ (markAdd factLevel) (RS.toList eAdds)
                  return (e:plan,gs')

  -- insert goals into the goal set for the level where they become true
  filterGoals factLevel gs f =
    do Fact { .. } <- readArray cgFacts f

       isTrue <- readIORef fIsTrue
       l      <- readIORef fLevel

       -- isTrue /= factLevel - 2   some other action already achieved this fact
       -- l /= 0                    this is not an initial fact
       if isTrue /= factLevel - 2 && l /= 0
          then return (IM.insertWith mappend l (RS.singleton f) gs)
          else return gs


  -- mark the fact as being added at i - 2, and i
  --
  --  i      (isGoal) prevents achievers from being selected for facts that are
  --         already true
  --  i - 2  preconditions achieved by actions ahead of this one should not be
  --         considered new goals
  markAdd i f =
    do Fact { .. } <- readArray cgFacts f
       writeIORef fIsGoal True    -- mark at i
       writeIORef fIsTrue (i - 2) -- mark at i - 2


  -- pick the best effect that achieved this goal in the preceding effect
  -- layer, using the difficulty heuristic
  pickBest _ []        = fail "extractPlan: invalid connection graph"
  pickBest _ [ref]     = return ref
  pickBest effLevel es = snd `fmap` foldM check (maxBound,undefined) es
    where
    check (d,e) r =
      do Effect { .. } <- readArray cgEffects r
         l <- readIORef eLevel
         if effLevel /= l
            then return (d,e)
            else do d' <- difficulty cg r
                    let acc | d' < d    = (d',r)
                            | otherwise = (d,e)
                    return $! acc


-- Helpful Actions -------------------------------------------------------------

helpfulActions :: ConnGraph -> RelaxedPlan -> GoalSet -> IO [EffectRef]
helpfulActions cg es gs =
  do l1 <- layer1 cg es
     case IM.lookup 2 gs of
       Just g1 -> filterM (isHelpful g1) l1
       _       -> return es

  where
  isHelpful goals ref =
    do Effect { .. } <- readArray (cgEffects cg) ref
       return (not (RS.null (RS.intersection goals eAdds)))


-- | These are the actions of the first layer.
layer1 :: ConnGraph -> RelaxedPlan -> IO [EffectRef]
layer1 ConnGraph { .. } = loop []
  where
  loop acc (e:es) = 
    do Effect { .. } <- readArray cgEffects e
       l <- readIORef eLevel
       if l == 1
          then loop (e:acc) es
          else return (reverse acc)

  loop acc [] = return (reverse acc)
