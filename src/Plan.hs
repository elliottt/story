{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import           Types
import qualified Unify

import           Control.Applicative
import           Data.Foldable ( foldMap )
import           Data.List ( sortBy )
import           Data.Graph
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Data.Monoid ( mappend )
import qualified Data.Set as Set
import           MonadLib

import Debug.Trace


type Plan = [Action]

pop :: Domain -> Assumps -> Goals -> Maybe Plan
pop d as gs = runPlanM d as $
  do solveGoals (map (Goal Finish) gs)
     rw <- PlanM get
     zonk (orderedActions rw)


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh     :: Int
             , rwEnv       :: Unify.Env
             , rwDomain    :: Domain
             , rwAssumps   :: Map.Map String [Assump]
             , rwActions   :: Set.Set Action
             , rwLinks     :: Set.Set CausalLink
             , rwOrderings :: Map.Map Action (Set.Set Action)
             } deriving (Show)

orderedActions :: RW -> [Action]
orderedActions RW { .. } = [ act | vert <- topSort graph
                                 , let (act,_,_) = fromVertex vert ]
  where
  (graph, fromVertex, _) = graphFromEdges edges

  edges = [ (act, act, Set.toList as)
          | act <- Set.toList rwActions
          , let as = Map.findWithDefault Set.empty act rwOrderings ]

data Assump = Assump { aFrom :: Action
                     , aPred :: Pred
                     } deriving (Show,Eq,Ord)

data Goal = Goal { gFrom :: Action
                 , gPred :: Pred
                 } deriving (Show,Eq,Ord)

runPlanM :: Domain -> Assumps -> PlanM a -> Maybe a
runPlanM d as m =
  case runId (findOne (runStateT rw (unPlanM m))) of
    Just (a,_) -> Just a
    Nothing    -> Nothing
  where
  rw = RW { rwFresh     = 0
          , rwEnv       = Map.empty
          , rwDomain    = d
          , rwAssumps   = baseAssumps
          , rwActions   = Set.fromList [Start,Finish]
          , rwLinks     = Set.empty
          , rwOrderings = Map.singleton Start (Set.singleton Finish)
          }

  baseAssumps =
    Map.fromListWith (++) [ (n,[Assump Start p]) | p@(Pred _ n _) <- as ]

getEnv :: PlanM Unify.Env
getEnv  = PlanM (rwEnv `fmap` get)

instId :: PlanM Int
instId  = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (rwFresh rw)

addAction :: Action -> PlanM ()
addAction act = PlanM $ do rw <- get
                           set rw { rwActions = Set.insert act (rwActions rw) }

before :: Action -> Action -> PlanM ()
before a b = PlanM $
  do rw @ RW { .. } <- get
     set rw
       { rwOrderings = Map.insertWith mappend a (Set.singleton b) rwOrderings }

-- | Insert a causal link between the action and the goal that it addresses.
link :: Action -> Goal -> PlanM ()
link act Goal { .. } = PlanM $
  do rw @ RW { .. } <- get
     set rw { rwLinks = Set.insert (Link act gPred gFrom) rwLinks }

assumpsFor :: String -> PlanM [Assump]
assumpsFor n = PlanM $ do RW { .. } <- get
                          return (Map.findWithDefault [] n rwAssumps)

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
       Left err   -> mzero

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

solveGoals :: [Goal] -> PlanM ()

solveGoals (g:gs) =
  do gs' <- solveGoal g
     solveGoals (gs ++ gs')

solveGoals [] =
     return ()

solveGoal :: Goal -> PlanM [Goal]
solveGoal g @ Goal { .. } =
  do (act,gs) <- msum [ do a <- byAssumption g
                           return (a,[])
                      , byNewAction g ]
     act `before` gFrom
     act `link` g

     return gs

-- | Solve a goal by a result that already exists in the plan.
byAssumption :: Goal -> PlanM Action
byAssumption Goal { .. } =
  do as <- assumpsFor (predName gPred)
     msum [ match gPred aPred >> return aFrom | Assump { .. } <- as ]

-- | Solve a goal, by generating a new action, and returning the additional
-- goals it generated.
byNewAction :: Goal -> PlanM (Action,[Goal])
byNewAction g @ Goal { .. } =
  do (ps,Operator { .. }) <- findAction g
     i                    <- instId
     let act = Inst i oName ps
     addAction act
     Start `before` act
     act   `before` Finish
     return (act, [ Goal act p | p <- oPrecond ])


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

testDomain = [buy,go]

testAssumps = [ Pred True "At" ["Home"]
              , Pred True "Sells" ["SM","Milk"]
              , Pred True "Sells" ["SM","Banana"]
              , Pred True "Sells" ["HW","Drill"]
              ]

testGoals = [ Pred True "Have" ["Milk"]
            , Pred True "Have" ["Banana"]
            , Pred True "Have" ["Drill"]
            ]

test = pop testDomain testAssumps testGoals
