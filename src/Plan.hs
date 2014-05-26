{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import           Pretty
import           PlanState
import           Types
import qualified Unify

import           Control.Applicative
import           Data.Foldable ( forM_ )
import qualified Data.Set as Set
import           MonadLib hiding ( forM_ )

import           Debug.Trace


pop :: Domain -> Assumps -> Goals -> Maybe [Action]
pop d as gs = runPlanM d p $
  do solveGoals goals
     zonk =<< fromPlan orderedActions
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


fromPlan :: (Plan -> a) -> PlanM a
fromPlan f = PlanM (f . rwPlan <$> get)

updatePlan_ :: (Plan -> Plan) -> PlanM ()
updatePlan_ f = PlanM $ do rw <- get
                           set $! rw { rwPlan = f (rwPlan rw) }

updatePlan :: (Plan -> (Plan,a)) -> PlanM a
updatePlan f = PlanM $ do rw <- get
                          let (p',a) = f (rwPlan rw)
                          set $! rw { rwPlan = p' }
                          return a

getBinds :: PlanM Unify.Env
getBinds  = fromPlan getBindings

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

freshInst :: Schema Operator -> PlanM (Action,Operator)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     ix <- nextId
     let oper = inst ts a
     return (Inst ix (oName oper) ts, oper)

getDomain :: PlanM Domain
getDomain  = PlanM (rwDomain <$> get)

-- XXX extending the binding environment might invalidate the causal links.
-- What's the best way to detect this?
match :: Unify.Unify tm => tm -> tm -> PlanM ()
match l r =
  do bs <- getBinds
     case Unify.match bs l r of
       Right bs' -> setBinds bs'
       Left _    -> mzero

unify :: (Unify.Unify tm, PP tm) => tm -> tm -> PlanM ()
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

dbg :: Show a => String -> a -> PlanM ()
dbg l a = traceM (l ++ ": " ++ show a)

zonkDbg :: (PP a, Unify.Zonk a) => String -> a -> PlanM ()
zonkDbg l a = do a' <- zonk a
                 traceM (show (hang (text l <> char ':') 2 (pp a')))


-- Planner ---------------------------------------------------------------------

-- | Solve a series of goals.
solveGoals :: [Goal] -> PlanM ()

solveGoals (g:gs) =
  do newGoals <- solveGoal g

     resolveThreats

     guard =<< fromPlan planConsistent

     solveGoals (gs ++ newGoals)

solveGoals [] =
     return ()

solveGoal :: Goal -> PlanM [Goal]
solveGoal g =
  do (s_add,gs) <- msum [ byAssumption g, byNewStep g ]

     updatePlan_ ( (s_add `isBefore` gSource g)
                 . addLink (Link s_add (gPred g) (gSource g)) )

     return gs


byAssumption :: Goal -> PlanM (Action,[Goal])
byAssumption Goal { .. } =
  do candidates <- fromPlan getActions
     msum (map tryAssump candidates)
  where
  tryAssump (act,node) =
    do msum [ unify gPred q | q <- effects node ]
       return (act, [])


byNewStep :: Goal -> PlanM (Action,[Goal])
byNewStep Goal { .. } =
  do dom <- getDomain
     msum (map tryInst dom)
  where
  tryInst s =
    do (act,op) <- freshInst s
       msum [ match q gPred | q <- oPostcond op ]

       gs <- updatePlan (addAction act op)
       updatePlan_ ( (Start `isBefore` act) . (act `isBefore` Finish) )

       return (act,gs)


resolveThreats :: PlanM ()
resolveThreats  =
  do as    <- fromPlan getActions
     links <- fromPlan getLinks
     bs    <- getBinds

     let unifies p q = case Unify.mgu bs p q of
                         Right {} -> True
                         Left {}  -> False

         isThreatened act es (Link l p r) =
           l /= act &&
           r /= act &&
           any (unifies (predNegate p)) es

         threats = [ (act,link) | (act,node) <- as
                                , link       <- Set.toList links
                                , isThreatened act (effects node) link ]

     unless (null threats) $
       do forM_ threats $ \ (act,Link l _ r) ->
            do f <- msum [ do guard (r /= Finish)
                              return (r `isBefore` act)
                         , do guard (l /= Start)
                              return (act `isBefore` l)
                         ]
               updatePlan_ f


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
             , Pred True "At" ["Home"]
             , Pred True "Have" ["Banana"]
             , Pred True "Have" ["Drill"]
             ]

test :: IO ()
test = case pop testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"
