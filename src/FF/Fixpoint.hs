{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module FF.Fixpoint where

import           FF.ConnGraph
import qualified FF.RefSet as RS

import           Control.Monad ( unless )
import           Data.Array
import           Data.IORef ( writeIORef, readIORef )
import           Data.Monoid ( mempty, mconcat )


-- Predicates ------------------------------------------------------------------

-- | Reset all references in the plan graph to their initial state.
resetConnGraph :: ConnGraph -> IO ()
resetConnGraph ConnGraph { .. } =
  do amapM_ resetFact   cgFacts
     amapM_ resetOper   cgOpers
     amapM_ resetEffect cgEffects

resetFact :: Fact -> IO ()
resetFact Fact { .. } =
     writeIORef fLevel maxBound

resetOper :: Oper -> IO ()
resetOper Oper { .. } = return ()

resetEffect :: Effect -> IO ()
resetEffect Effect { .. } =
  do writeIORef eLevel maxBound
     writeIORef eActivePre 0


-- | Loop until the goal state is activated in the connection graph.  As the
-- connection graph should only be built from domains that can activate all
-- facts, and delete effects are ignored, this operation will terminate.
buildFixpoint :: ConnGraph -> State -> Goals -> IO ()
buildFixpoint gr s0 g =
  do resetConnGraph gr
     loop 0 s0

  where
  loop level facts =
    do effs <- mconcat `fmap` mapM (activateFact gr level) (RS.toList facts)
       done <- allGoalsReached gr g
       unless done $
         do facts' <- mconcat `fmap` mapM (activateEffect gr level) (RS.toList effs)

            if RS.null facts'
               then return ()
               else loop (level + 1) facts'


-- | All goals have been reached if they are all activated in the connection
-- graph.
allGoalsReached :: ConnGraph -> Goals -> IO Bool
allGoalsReached cg g = go goals
  where
  goals     = RS.toList g

  -- require that all goals have a level that isn't infinity.
  go (r:rs) = do let Fact { .. } = cgFacts cg ! r
                 l <- readIORef fLevel
                 if l < maxBound
                    then go rs
                    else return False

  go []     =    return True


-- | Set a fact to true at this level of the relaxed graph.  Return any effects
-- that were enabled by adding this fact.
activateFact :: ConnGraph -> Level -> FactRef -> IO Effects
activateFact ConnGraph { .. } level ref =
  do let Fact { .. } = cgFacts ! ref
     writeIORef fLevel level

     mconcat `fmap` mapM addedPrecond (RS.toList fAdd)

  where

  addedPrecond eff =
    do let Effect { .. } = cgEffects ! eff
       pcs <- readIORef eActivePre
       let pcs' = pcs + 1
       writeIORef eActivePre $! pcs'

       if pcs' == eNumPre
          then return (RS.singleton eff)
          else return mempty

-- | Add an effect at level i, and return all of its add effects.
activateEffect :: ConnGraph -> Level -> EffectRef -> IO Facts
activateEffect ConnGraph { .. } level ref =
  do let Effect { .. } = cgEffects ! ref
     writeIORef eLevel level
     return eAdds


-- Utilities -------------------------------------------------------------------

amapM_ :: (Enum i, Ix i) => (e -> IO ()) -> Array i e -> IO ()
amapM_ f arr = go lo
  where
  (lo,hi) = bounds arr

  go i | i > hi    = return ()
       | otherwise = do f (arr ! i)
                        go (succ i)
