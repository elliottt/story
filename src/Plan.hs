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
import           Data.Monoid ( mappend )
import qualified Data.Set as Set
import           MonadLib hiding ( forM_ )

import           Debug.Trace


pop :: Domain -> Assumps -> Goals -> Maybe [Step]
pop d as gs = runPlanM d p $
  do solveGoals Flaws { fOpenConditions = goals }
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

freshInst :: Schema Action -> PlanM (Step,Action)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     ix <- nextId
     let oper = inst ts a
     return (Inst ix (aName oper) ts, oper)

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
solveGoals :: Flaws -> PlanM ()
solveGoals flaws
  | noFlaws flaws =
    return ()

  | otherwise =
    do (g,flaws') <- nextOpenCondition flaws

       newFlaws <- solveGoal g

       resolveThreats

       guard =<< fromPlan planConsistent

       solveGoals (flaws' `mappend` newFlaws)


solveGoal :: Goal -> PlanM Flaws
solveGoal g =
  do (s_add,gs) <- msum [ byAssumption g, byNewStep g ]

     updatePlan_ ( (s_add `isBefore` gSource g)
                 . addLink (Link s_add (gPred g) (gSource g)) )

     return Flaws { fOpenConditions = gs }


byAssumption :: Goal -> PlanM (Step,[Goal])
byAssumption Goal { .. } =
  do candidates <- fromPlan getActions
     msum (map tryAssump candidates)
  where
  tryAssump (act,node) =
    do msum [ unify gPred q | q <- effects node ]
       return (act, [])


byNewStep :: Goal -> PlanM (Step,[Goal])
byNewStep Goal { .. } =
  do dom <- getDomain
     msum (map tryInst dom)
  where
  tryInst s =
    do (act,op) <- freshInst s
       msum [ match q gPred | q <- aEffect op ]

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

buy :: Schema Action
buy  = forall ["x", "store"] $ \ [x,store] ->
  emptyAction { aName    = "Buy"
              , aPrecond = [ PFormula $ Formula True "At"    [store]
                           , PFormula $ Formula True "Sells" [store,x] ]
              , aEffect  = [ PFormula $ Formula True "Have"  [x] ]
              }

go :: Schema Action
go  = forall ["x", "y"] $ \ [x,y] ->
  emptyAction { aName    = "Go"
              , aPrecond = [ PFormula $ Formula True  "At" [x] ]
              , aEffect  = [ PFormula $ Formula True  "At" [y]
                           , PFormula $ Formula False "At" [x] ]
              }

testDomain :: Domain
testDomain  = [buy,go]

testAssumps :: Assumps
testAssumps  = [ PFormula $ Formula True "At"    ["Home"]
               , PFormula $ Formula True "Sells" ["SM","Milk"]
               , PFormula $ Formula True "Sells" ["SM","Banana"]
               , PFormula $ Formula True "Sells" ["HW","Drill"]
               ]

testGoals :: Goals
testGoals  = [ PFormula $ Formula True "Have" ["Milk"]
             , PFormula $ Formula True "At" ["Home"]
             , PFormula $ Formula True "Have" ["Banana"]
             , PFormula $ Formula True "Have" ["Drill"]
             ]

-- testDomain =
--   [ forall [] $ \ [] ->
--     Operator { oName     = "RemoveSpareFromTrunk"
--              , oPrecond  = [ Pred True "At" ["Spare", "Trunk"] ]
--              , oPostcond = [ Pred True "At" ["Spare", "Ground"]
--                            , Pred False "At" ["Spare", "Trunk"] ]
--              }
--   , forall [] $ \ [] ->
--     Operator { oName     = "RemoveFlatFromAxel"
--              , oPrecond  = [ Pred True "At" ["Flat", "Axle"] ]
--              , oPostcond = [ Pred True "At" ["Flat", "Ground"]
--                            , Pred False "At" ["Flat", "Axle"] ]
--              }
-- 
--   , forall [] $ \ [] ->
--     Operator { oName     = "PutSpareOnAxle"
--              , oPrecond  = [ Pred True  "At" ["Spare", "Ground"]
--                            , Pred False "At" ["Flat", "Axle"] ]
--              , oPostcond = [ Pred True  "At" ["Spare", "Axle"]
--                            , Pred False "At" ["Spare", "Ground"] ]
--              }
--   , forall [] $ \ [] ->
--     Operator { oName = "LeaveOvernight"
--              , oPrecond = []
--              , oPostcond = [ Pred False "At" ["Spare", "Ground"]
--                            , Pred False "At" ["Spare", "Axle"]
--                            , Pred False "At" ["Spare", "Trunk"]
--                            , Pred False "At" ["Flat", "Ground"]
--                            , Pred False "At" ["Flat", "Axle"] ]
--              }
--   ]
-- 
-- testAssumps = [ Pred True "At" ["Flat", "Axle"]
--               , Pred True "At" ["Spare", "Trunk"] ]
-- 
-- testGoals = [ Pred True "At" ["Spare", "Axle"] ]

test :: IO ()
test = case pop testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"


-- -----------------------------------------------------------------------------
