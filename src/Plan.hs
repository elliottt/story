{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import           Types
import qualified Unify

import           Control.Applicative
import qualified Data.Map as Map
import           Data.Monoid ( mempty )
import qualified Data.Set as Set
import           MonadLib

import Debug.Trace


type Plan = [Action]

pop :: Domain -> Assumps -> Goals -> Maybe Plan
pop d as gs = runPlanM d as (solveGoals (map (Goal Finish) gs))


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh     :: Int
             , rwEnv       :: Unify.Env
             , rwDomain    :: Domain
             , rwActions   :: Set.Set Action
             , rwLinks     :: Set.Set CausalLink
             , rwOrderings :: Map.Map Action [Action]
             }

orderedActions :: RW -> [Action]
orderedActions RW { .. } = go Start
  where
  go Finish = []
  go i = case Map.lookup i rwOrderings of
           Just is -> i : is ++ concatMap go is

           -- this shouldn't happen
           Nothing -> []


data Goal = Goal { gAction :: Action
                 , gPred   :: Pred
                 } deriving (Show,Eq,Ord)

runPlanM :: Domain -> Assumps -> PlanM a -> Maybe a
runPlanM d as m = fmap fst (runId (findOne (runStateT rw (unPlanM m))))
  where
  rw = RW { rwFresh     = 0
          , rwEnv       = Map.empty
          , rwDomain    = d
          , rwActions   = Set.fromList [Start,Finish]
          , rwLinks     = Set.empty
          , rwOrderings = Map.singleton Start [Finish]
          }

getEnv :: PlanM Unify.Env
getEnv  = PlanM (rwEnv `fmap` get)

instId :: PlanM Int
instId  = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (rwFresh rw)

fresh :: Var -> PlanM Term
fresh v = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (TVar v { varIndex = rwFresh rw })

fresh_ :: PlanM Term
fresh_  = fresh (Var Nothing 0)

freshInst :: Inst a => Schema a -> PlanM ([Term],a)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     return (ts,inst ts a)

match :: Unify.Unify tm => tm -> tm -> PlanM ()
match l r = PlanM $
  do rw <- get
     case Unify.match (rwEnv rw) l r of
       Right env' -> set rw { rwEnv = env' }
       Left err   -> traceShow err mzero

unify :: Unify.Unify tm => tm -> tm -> PlanM ()
unify l r = PlanM $
  do rw <- get
     case Unify.mgu (rwEnv rw) l r of
       Right env' -> set rw { rwEnv = env' }
       Left _     -> mzero

zonk :: Unify.Zonk tm => tm -> PlanM tm
zonk tm = PlanM $
  do rw <- get
     case Unify.zonk (rwEnv rw) tm of
       Right tm' -> return tm'
       Left _    -> mzero

-- | Find an operator that satisfies the goal, and add its preconditions as
-- additional goals of the chosen operator.
findAction :: Goal -> PlanM ([Term],Operator)
findAction Goal { .. } =
  do rw <- PlanM get
     msum [ achieves op gPred | op <- rwDomain rw ]

-- | Return the instantiated action that achieves the condition p.  If the
-- action does not achieve p, fail wiht mzero.
achieves :: Schema Operator -> Pred -> PlanM ([Term],Operator)
achieves op p =
  do (ps,iop) <- freshInst op
     _        <- msum [ match c p | c <- oPostcond iop ]
     zop      <- zonk iop
     return (ps,zop)


-- Planner ---------------------------------------------------------------------

solveGoals :: [Goal] -> PlanM [Action]

solveGoals (g:gs) =
  do gs' <- solveGoal g
     solveGoals (gs ++ gs')

solveGoals [] =
  do rw <- PlanM get
     return (orderedActions rw)


-- | Solve a goal, returning any generated goals.
solveGoal :: Goal -> PlanM [Goal]
solveGoal g =
  do (ps,op) <- findAction g
     i       <- instId
     let mkGoal = Goal (Inst i (oName op) ps)
     return (map mkGoal (oPrecond op))


-- Testing ---------------------------------------------------------------------

move = forall ["who", "a", "b"] $ \ [who,a,b] -> Operator
  { oName     = "move"
  , oPrecond  = [ Pred True "At" [who,a] ]
  , oPostcond = [ Pred True  "At" [who,b]
                , Pred False "At" [who,a] ]
  }

test = pop [move] [Pred True "At" ["me", "home"]]
                  [Pred True "At" ["me", "work"]]
