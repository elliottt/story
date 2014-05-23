{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import           PlanState
import           Types
import qualified Unify

import           Control.Applicative
import           MonadLib


pop :: Domain -> Assumps -> Goals -> Maybe Plan
pop d as gs = runPlanM d p $
  do solveGoals goals
     PlanM (rwPlan `fmap` get)
  where
  (p,goals) = initialPlan as gs


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh  :: Int
             , rwDomain :: Domain
             , rwPlan   :: Plan
             } deriving (Show)

runPlanM :: Domain -> Plan -> PlanM a -> Maybe a
runPlanM d p m =
  case runId (findOne (runStateT rw (unPlanM m))) of
    Just (a,_) -> Just a
    Nothing    -> Nothing
  where
  rw = RW { rwFresh  = 0
          , rwDomain = d
          , rwPlan   = p
          }


getBinds :: PlanM Unify.Env
getBinds  = PlanM (getBindings . rwPlan <$> get)

setBinds :: Unify.Env -> PlanM ()
setBinds bs = PlanM $ do rw <- get
                         set rw { rwPlan = setBindings bs (rwPlan rw) }

nextId :: PlanM Int
nextId  = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (rwFresh rw)

fresh :: Var -> PlanM Term
fresh v = do ix <- nextId
             return (TVar v { varIndex = ix })

fresh_ :: PlanM Term
fresh_  = fresh (Var Nothing undefined)

freshInst :: Inst a => Schema a -> PlanM ([Term],a)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     return (ts,inst ts a)

-- XXX extending the binding environment might invalidate the causal links.
-- What's the best way to detect this?
match :: Unify.Unify tm => tm -> tm -> PlanM ()
match l r =
  do bs <- getBinds
     case Unify.match bs l r of
       Right bs' -> setBinds bs'
       Left _    -> mzero

unify :: Unify.Unify tm => tm -> tm -> PlanM ()
unify l r =
  do bs <- getBinds
     case Unify.mgu bs l r of
       Right bs' -> setBinds bs'
       Left _    -> mzero

zonk :: Unify.Zonk tm => tm -> PlanM tm
zonk tm =
  do bs <- getBinds
     case Unify.zonk bs tm of
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

-- | Solve a series of goals.
solveGoals :: [Goal] -> PlanM ()

solveGoals (g:gs) =
  do gs' <- solveGoal g
     solveGoals (gs ++ gs')

solveGoals [] =
     return ()


-- | Solve a goal, yielding out any sub-goals.
solveGoal :: Goal -> PlanM [Goal]
solveGoal g =
  do (act,gs') <- msum [ do act <- byAssumption g
                            return (act,[])
                       , byNewAction g ]

     return gs'


-- | Solve a goal by an existing action.
byAssumption :: Goal -> PlanM Action
byAssumption Goal { .. } =
     mzero


-- | Solve a goal by introducing a new action, and returning any new goals it
-- introduces.
byNewAction :: Goal -> PlanM (Action, [Goal])
byNewAction Goal { .. } =
     mzero


-- Testing ---------------------------------------------------------------------

buy :: Schema Operator
buy  = forall ["x", "store"] $ \ [x,store] ->
  Operator { oName     = "Buy"
           , oPrecond  = [ Pred True "At" [store], Pred True "Sells" [store,x] ]
           , oPostcond = [ Pred True "Have" [x] ]
           }

go :: Schema Operator
go  = forall ["x", "y"] $ \ [x,y] ->
  Operator { oName     = "Go"
           , oPrecond  = [ Pred True "At" [x] ]
           , oPostcond = [ Pred True "At" [y], Pred False "At" [x] ]
           }

testDomain :: Domain
testDomain  = [buy,go]

testAssumps :: Assumps
testAssumps  = [ Pred True "At" ["Home"]
               , Pred True "Sells" ["SM","Milk"]
               , Pred True "Sells" ["SM","Banana"]
               , Pred True "Sells" ["HW","Drill"]
               ]

testGoals :: Goals
testGoals  = [ Pred True "Have" ["Milk"]
             -- , Pred True "Have" ["Banana"]
             , Pred True "Have" ["Drill"]
             ]

test :: IO ()
test = case pop testDomain testAssumps testGoals of
  Just plan -> print (orderedActions plan)
  Nothing   -> putStrLn "No plan"
