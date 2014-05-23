{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import           Pretty
import           Types
import qualified Unify

import           Control.Applicative
import           Data.Foldable ( foldMap, asum )
import qualified Data.Foldable as F
import           Data.List ( partition )
import           Data.Graph
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe, maybeToList )
import           Data.Monoid ( mappend )
import qualified Data.Set as Set
import           Data.Tree
import           MonadLib

import Debug.Trace


type Plan = [Action]

pop :: Domain -> Assumps -> Goals -> Maybe Plan
pop d as gs = runPlanM d $
  do
     addAction Start Operator { oName     = "Start"
                              , oPrecond  = []
                              , oPostcond = as }

     addAction Finish Operator { oName     = "Finish"
                               , oPrecond  = gs
                               , oPostcond = [] }

     Start `before` Finish

     solveGoals (map (Goal Finish) gs)
     rw <- PlanM get
     zonk (orderedActions rw)


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh     :: Int
             , rwEnv       :: Unify.Env
             , rwDomain    :: Domain
             , rwActions   :: Actions
             , rwLinks     :: Set.Set CausalLink
             , rwOrderings :: Orderings
             } deriving (Show)

type Actions = Map.Map Action Operator

type Orderings = Map.Map Action (Set.Set Action)

ordEdges :: Actions -> Orderings -> [(Action, Action, [Action])]
ordEdges acts ords =
  [ (act, act, Set.toList as)
  | act <- Map.keys acts
  , let as = Map.findWithDefault Set.empty act ords ]

allAfter :: Actions -> Orderings -> Action -> [Action]
allAfter acts ords act = [ a | key  <- maybeToList (toVertex act)
                             , vert <- reachable graph key
                             , let (a,_,_) = fromVertex vert ]
  where
  (graph, fromVertex, toVertex) = graphFromEdges (ordEdges acts ords)

noOrdCycles :: Actions -> Orderings -> Bool
noOrdCycles acts ords = all notRecursive (stronglyConnComp (ordEdges acts ords))
  where
  notRecursive AcyclicSCC {} = True
  notRecursive CyclicSCC {}  = False

orderedActions :: RW -> [Action]
orderedActions RW { .. } = [ act | vert <- topSort graph
                                 , let (act,_,_) = fromVertex vert ]
  where
  (graph, fromVertex, _) = graphFromEdges (ordEdges rwActions rwOrderings)


data Goal = Goal { gFrom :: Action
                 , gPred :: Pred
                 } deriving (Show,Eq,Ord)

instance PP Goal where
  pp Goal { .. } = pp gPred <+> text "from" <+> pp gFrom

instance Unify.Zonk Goal where
  zonk' Goal { .. } = Goal <$> Unify.zonk' gFrom
                           <*> Unify.zonk' gPred

runPlanM :: Domain -> PlanM a -> Maybe a
runPlanM d m =
  case runId (findOne (runStateT rw (unPlanM m))) of
    Just (a,_) -> Just a
    Nothing    -> Nothing
  where
  rw = RW { rwFresh     = 0
          , rwEnv       = Map.empty
          , rwDomain    = d
          , rwActions   = Map.empty
          , rwLinks     = Set.empty
          , rwOrderings = Map.empty
          }


getEnv :: PlanM Unify.Env
getEnv  = PlanM (rwEnv `fmap` get)

instId :: PlanM Int
instId  = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (rwFresh rw)

addAction :: Action -> Operator -> PlanM ()
addAction act oper = PlanM $
  do rw <- get
     set rw { rwActions = Map.insert act oper (rwActions rw) }

getAction :: Action -> PlanM Operator
getAction act =
  do RW { .. } <- PlanM get
     case Map.lookup act rwActions of
       Just oper -> return oper
       Nothing   -> mzero

-- | Add an ordering constraint.  Fails when the constraint introduces a cycle.
before :: Action -> Action -> PlanM ()
before a b = PlanM $
  do rw <- get
     let ords' = Map.insertWith mappend a (Set.singleton b) (rwOrderings rw)
     unless (noOrdCycles (rwActions rw) ords') $
       do traceM "ord cycles detected"
          mzero
     set rw { rwOrderings = ords' }

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

-- XXX extending the binding environment might invalidate the causal links.
-- What's the best way to detect this?
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

-- | Find an existing action that achieves p.
filterAssumps :: Pred -> PlanM (Action,Operator)
filterAssumps p =
  do RW { .. } <- PlanM get
     msum [ check e | e@(_,oper) <- Map.toList rwActions ]
  where
  check res@(_,Operator { .. }) =
    do assump <- msum [ return pred | pred <- oPostcond ]
       match p assump
       dbg "using assumption" res
       return res

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
                      , byNewAction g
                      , do dbg "FAILED TO SOLVE GOAL" g
                           mzero ]
     act `before` gFrom
     act `link` g

     dbg "new-goals" gs

     return gs

-- | Solve a goal by a result that already exists in the plan.
byAssumption :: Goal -> PlanM Action
byAssumption Goal { .. } =
  do (act,_) <- filterAssumps gPred
     return act

-- | Solve a goal, by generating a new action, and returning the additional
-- goals it generated.
byNewAction :: Goal -> PlanM (Action,[Goal])
byNewAction g @ Goal { .. } =
  do (ps,op@Operator { .. }) <- findAction g
     i                       <- instId
     let act = Inst i oName ps
     addAction act op
     Start `before` act
     act   `before` Finish
     return (act, [ Goal act p | p <- oPrecond ])

-- | Insert a causal link between the action and the goal that it addresses,
-- after validating its interaction with existing links.
link :: Action -> Goal -> PlanM ()
link act Goal { .. } =
  do resolveThreats cl
     PlanM $ do rw <- get
                set rw { rwLinks = Set.insert cl (rwLinks rw) }
  where
  cl = Link act gPred gFrom

resolveThreats :: CausalLink -> PlanM ()
resolveThreats cl @ (Link l _ r) =
  do rw @ RW { .. }  <- PlanM get
     Operator { .. } <- getAction r


     dbg "link" cl

     let matches p q = case Unify.match rwEnv p q of
                         Right {} -> True
                         Left {}  -> False

         -- links are threatened when the negation of their effect is matched in
         -- the postcondition of the action being used
         threatens (Link _ p _) = matches (predNegate p)

         isThreatened l = any (threatens l) oPostcond

         (ts,ls) = Set.partition isThreatened rwLinks

     dbg "threats" ts

     unless (Set.null ts) $
       msum [ F.mapM_ (\Link{ .. } -> r       `before` clLeft) ts
            , F.mapM_ (\Link{ .. } -> clRight `before` l)      ts ]

     PlanM (set rw { rwLinks = Set.insert cl rwLinks })

dbg :: (Unify.Zonk a, PP a) => String -> a -> PlanM ()
dbg l a = do a' <- zonk a
             traceShow (text l <> char ':' <+> pp a') return ()


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
            -- , Pred True "Have" ["Banana"]
            , Pred True "Have" ["Drill"]
            ]

test = case pop testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"
