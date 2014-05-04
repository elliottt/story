{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Plan where

import           Types
import qualified Unify

import           Control.Applicative
import           Data.Monoid ( mempty )
import qualified Data.Set as Set
import           MonadLib


pop :: Domain -> Plan -> Maybe Plan
pop d p = runPlanM p (solveGoals d p)


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh :: Int
             , rwEnv   :: Unify.Env
             , rwPlan  :: Plan
             }

runPlanM :: Plan -> PlanM a -> Maybe a
runPlanM p m = fmap fst (runId (findOne (runStateT rw (unPlanM m))))
  where
  rw = RW { rwFresh = 0
          , rwEnv   = mempty
          , rwPlan  = p
          }

getEnv :: PlanM Unify.Env
getEnv  = PlanM (rwEnv `fmap` get)

fresh :: Var -> PlanM Term
fresh v = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (TVar v { varIndex = rwFresh rw })

fresh_ :: PlanM Term
fresh_  = fresh (Var Nothing 0)

freshInst :: Inst a => Schema a -> PlanM a
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     return (inst ts a)

match :: Unify.Unify tm => tm -> tm -> PlanM ()
match l r = PlanM $
  do rw <- get
     case Unify.match (rwEnv rw) l r of
       Right env' -> set rw { rwEnv = env' }
       Left _     -> mzero

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

-- | Return the instantiated action that achieves the condition p.  If the
-- action does not achieve p, fail wiht mzero.
achieves :: Schema Operator -> Pred -> PlanM Operator
achieves op p =
  do iop <- freshInst op
     msum [ match c p >> zonk iop | c <- oPostcond iop ]


-- Planner ---------------------------------------------------------------------

solveGoals :: Domain -> Plan -> PlanM Plan
solveGoals d p
  | Set.null (planSubGoals p) = return p
  | otherwise                 =
    do (p',g) <- chooseSubGoal p
       undefined

chooseSubGoal :: Plan -> PlanM (Plan,SubGoal)
chooseSubGoal p = undefined


-- Testing ---------------------------------------------------------------------

test = Forall [a,b] Operator
  { oName     = "test"
  , oPrecond  = []
  , oPostcond = [Pred True "At" [TGen a, TGen b]]
  }
  where
  a = Var (Just "a") 0
  b = Var (Just "b") 1
