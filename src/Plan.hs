{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Plan where

import           Types
import qualified Unify

import           Control.Applicative
import qualified Data.Map as Map
import           Data.Monoid ( mempty )
import qualified Data.Set as Set
import           MonadLib


type Plan = [Action]

pop :: Domain -> Assumps -> Goals -> Maybe Plan
pop d as gs = runPlanM d as (solveGoals (map (Goal Finish) gs))


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh     :: Int
             , rwEnv       :: Unify.Env
             , rwActions   :: Set.Set Action
             , rwLinks     :: Set.Set CausalLink
             , rwOrderings :: Set.Set Constraint
             , rwAgenda    :: Set.Set Goal
             }

data Goal = Goal { gAction :: Action
                 , gTerm   :: Term
                 } deriving (Show,Eq,Ord)

runPlanM :: Domain -> Assumps -> PlanM a -> Maybe a
runPlanM p as m = fmap fst (runId (findOne (runStateT rw (unPlanM m))))
  where
  rw = RW { rwFresh     = 0
          , rwEnv       = Map.empty
          , rwActions   = Set.fromList [Start,Finish]
          , rwLinks     = Set.empty
          , rwOrderings = Set.singleton (Start :< Finish)
          , rwAgenda    = Set.empty
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

solveGoals :: [Goal] -> PlanM [Action]
solveGoals _ = undefined


-- Testing ---------------------------------------------------------------------

test = Forall [a,b] Operator
  { oName     = "test"
  , oPrecond  = []
  , oPostcond = [Pred True "At" [TGen a, TGen b]]
  }
  where
  a = Var (Just "a") 0
  b = Var (Just "b") 1
