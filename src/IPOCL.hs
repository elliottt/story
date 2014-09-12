{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternSynonyms #-}

module IPOCL where

import qualified DiscTrie as T
import           Pretty
import           Plan
import           Types
import qualified Unify

import           Control.Applicative
import           Data.Foldable ( forM_ )
import           Data.Maybe ( mapMaybe )
import           Data.Monoid ( mempty, mappend )
import qualified Data.Set as Set
import qualified Data.Traversable as T
import           MonadLib hiding ( forM_ )

import           Debug.Trace


ipocl :: Domain -> Assumps -> Goals -> Maybe [Step]
ipocl d as gs = runPlanM as d p $
  do solveGoals flaws
     zonk =<< fromPlan orderedActions
  where
  (p,flaws) = initialPlan as gs


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh  :: Int
             , rwDomain :: T.Domain
             , rwPlan   :: Plan
             , rwFacts  :: T.Facts
               -- ^ Static knowledge from the initial state
             } deriving (Show)

runPlanM :: Assumps -> Domain -> Plan -> PlanM a -> Maybe a
runPlanM as d p m =
  case runId (findOne (runStateT rw (unPlanM m))) of
    Just (a,_) -> Just a
    Nothing    -> Nothing
  where
  rw = RW { rwFresh  = 0
          , rwDomain = T.mkDomain d
          , rwPlan   = p
          , rwFacts  = T.mkFacts as
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

getFacts :: PlanM T.Facts
getFacts  = PlanM $ do RW { .. } <- get
                       return rwFacts

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

getDomain :: PlanM T.Domain
getDomain  = PlanM (rwDomain <$> get)

getNode :: Step -> PlanM Node
getNode step =
  do mb <- fromPlan (getAction step)
     case mb of
       Just node -> return node
       Nothing   -> error ("Invalid Step: " ++ show step)

lookupFrame :: FrameRef -> PlanM Frame
lookupFrame ref =
  do mb <- fromPlan (getFrame ref)
     case mb of
       Just frame -> return frame
       Nothing    -> error ("Invalid FrameRef: " ++ show ref)

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

solveGoals (FOpenCond g : flaws')

  | PNeq p q <- gGoal g =
    do --zonkDbg "Inequality" (gGoal g)
       (p',q') <- zonk (p,q)
       if ground p' && ground q'

          -- make sure that the two are different, and solve the goal
          then do guard (p' /= q')
                  solveGoals flaws'

          -- not enough information, defer the goal
          else    solveGoals (flaws' ++ [FOpenCond g])

  | otherwise =
    do -- zonkDbg "Open Condition" g
       newFlaws <- discoveryAndResolution (causalPlanning g)
       guard =<< fromPlan planConsistent
       solveGoals (flaws' ++ newFlaws)

solveGoals (FMotivation ref : flaws') =
  do frame <- lookupFrame ref
     -- zonkDbg "Motivation Flaw" frame
     newFlaws <- discoveryAndResolution (motivationPlanning ref frame)
     guard =<< fromPlan planConsistent
     solveGoals (flaws' ++ newFlaws)

solveGoals (FIntent step ref : flaws') =
  do frame <- lookupFrame ref
     -- zonkDbg "Intent Flaw" (step,fGoal frame)
     newFlaws <- frameSelection step ref frame
     solveGoals (flaws' ++ newFlaws)

solveGoals [] =
     return ()


-- Threat Resolution -----------------------------------------------------------

discoveryAndResolution :: PlanM (Bool,Step,Flaws) -> PlanM Flaws
discoveryAndResolution body =
  do (isNew,s_add,flaws) <- body

     frameFlaws <- if isNew
                      then discoverFrameFlaws s_add
                      else return mempty

     intentFlaws <- discoverIntentFlaws s_add

     resolveCausalThreats

     return (flaws `mappend` frameFlaws `mappend` intentFlaws)


-- | Given a step that is new to the plan, derive frames of commitment for each
-- goal, and yield motivation flaws.
--
-- The new motivation flaw represents an opportunity to find a step that
-- motivates the final step of the new frame of commitment.
--
--  * Should intent effects be considered when producing a frame of commitment?
--
discoverFrameFlaws :: Step -> PlanM Flaws
discoverFrameFlaws s_add = discoverEffectFrame `mplus` noFrame
  where
  discoverEffectFrame =
    do node <- getNode s_add
       let Action { .. } = action node
       guard (not (null aActors))
       msum [ tryEffectFrame aActors p | p <- aEffect ]

  tryEffectFrame actors p =
    do refs <- updatePlan (addFrames (map mkFrame actors))
       return [ FMotivation ref | ref <- refs ]
    where
    mkFrame a = Frame { fSteps      = Set.empty
                      , fActor      = a
                      , fGoal       = p
                      , fFinal      = s_add
                      , fMotivation = Nothing
                      }

  addFrames frames plan = T.mapAccumL (flip addFrame) plan frames

  noFrame = return []


-- | Find all frames of commitment that could be used to explain s_add, and for
-- each one, emit an intent flaw.
discoverIntentFlaws :: Step -> PlanM Flaws
discoverIntentFlaws s_add =
  do -- first, find all frames that have a step that has an effect of s_add as a
     -- precondition
     cond1 <- fromPlan (sameIntent s_add)

     -- XXX cond1 only represents half of the picture when generating intent
     -- flaws

     -- generate intent flaws
     return [ FIntent s_add ref | ref <- Set.toList cond1 ]


resolveCausalThreats :: PlanM ()
resolveCausalThreats  =
  do threats <- causalThreats

     unless (null threats) $
       do forM_ threats $ \ (act,Link l _ r) ->
            do f <- msum [ do guard (r /= Finish)
                              return (r `isBefore` act)
                         , do guard (l /= Start)
                              return (act `isBefore` l)
                         ]
               updatePlan_ f

-- | Discover causal threats in the plan.
causalThreats :: PlanM [(Step,Link)]
causalThreats  =
  do as    <- fromPlan getActions
     links <- fromPlan getLinks
     bs    <- getBinds

     let unifies p q = case Unify.mgu bs p q of
                         Right {} -> True
                         Left {}  -> False

         isThreatened act es (Link l p r) =
           l /= act &&
           r /= act &&
           any (unifies (negPred p)) es

         threats = [ (act,link) | (act,node) <- as
                                , link       <- Set.toList links
                                , isThreatened act (effects node) link ]

     return threats


-- Operator Selection ----------------------------------------------------------

operatorSelection :: Pred -> PlanM (Bool,Step,Flaws)
operatorSelection goal =
  msum [ do res <- byAssumption goal
            return (False,res,mempty)
       , do (s_add,flaws) <- byNewStep goal
            return (True,s_add,flaws)
       ]


-- | Resolve an open condition by reusing an exising step in the plan.
byAssumption :: Pred -> PlanM Step
byAssumption goal =
  do candidates <- fromPlan getActions
     msum (map tryAssump candidates)
  where
  tryAssump (act,node) =
    do msum [ unify goal q | q <- effects node ]
       return act


-- | Resolve an open condition by adding a new step to the plan.
byNewStep :: Pred -> PlanM (Step,Flaws)
byNewStep goal =
  do dom <- getDomain
     msum (map tryInst (T.lookup goal dom))
  where
  tryInst s =
    do (act,op) <- freshInst s

       -- find an effect that matches the goal
       env <- getBinds
       case mapMaybe (isRelevant env) (aEffect op) of
         env' : _ -> setBinds env'
         []       -> mzero

       flaws <- updatePlan (addAction act op)
       updatePlan_ ( (Start `isBefore` act) . (act `isBefore` Finish) )

       -- when constraints exist, examine the facts to variable binding choices
       useConstraints act (aConstraints op)

       -- zonkDbg "New step" act

       return (act,flaws)

  isRelevant env q =
    case Unify.mgu env goal q of
      Right env' -> Just env'
      Left _     -> Nothing


useConstraints :: Step -> [Pred] -> PlanM ()
useConstraints from ps =
  do facts <- getFacts
     loop facts ps
  where
  loop facts (p:ps) = msum [ do unify p atom
                                loop facts ps
                           | atom <- T.lookup p facts ]
  loop _     []     = return ()


-- Causal Planning -------------------------------------------------------------

causalPlanning :: Goal -> PlanM (Bool,Step,Flaws)
causalPlanning Goal { .. } =
  do res@(isNew,s_add,flaws) <- operatorSelection gGoal

     updatePlan_ ( (s_add `isBefore` gSource)
                 . addLink (Link s_add gGoal gSource) )

     return res


-- Motivation Planning ---------------------------------------------------------

-- | A frame of commitment that currently lacks a motivating step.
motivationPlanning :: FrameRef -> Frame -> PlanM (Bool,Step,Flaws)
motivationPlanning ref c @ Frame { .. } =
  do let goal = PIntends fActor fGoal

     res @ (isNew,s_add,flaws) <- operatorSelection goal

     let link = Link s_add fGoal fFinal

     updatePlan_ ( (s_add `isBeforeFrame` c)
                 . addLink link
                 . modifyFrame ref (\ f -> f { fMotivation = Just s_add })
                 )

     return res


-- Intent Planning -------------------------------------------------------------

frameSelection :: Step -> FrameRef -> Frame -> PlanM Flaws
frameSelection step ref frame =
  msum [ do motivation <- case fMotivation frame of
                            Just s  -> return s
                            Nothing -> mzero

            -- add the step to the frame, and order it after the motivating
            -- step
            updatePlan_ ( modifyFrame ref addStep
                        . (motivation `isBefore` step) )

            -- XXX order frames WRT each other

            -- XXX generate intent flaws for causal links with the same
            -- character that occur before the new step

            return []

       ,    return []
       ]
  where
  addStep frame = frame { fSteps = Set.insert step (fSteps frame) }


-- Testing ---------------------------------------------------------------------

-- buy :: Schema Action
-- buy  = forall ["x", "store"] $ \ [x,store] ->
--   emptyAction { aName    = "Buy"
--               , aPrecond = [ Pred True "At"    [store]
--                            , Pred True "Sells" [store,x] ]
--               , aEffect  = [ EPred $ Pred True "Have"  [x] ]
--               }

-- go :: Schema Action
-- go  = forall ["x", "y"] $ \ [x,y] ->
--   emptyAction { aName    = "Go"
--               , aPrecond = [ Pred True  "At" [x] ]
--               , aEffect  = [ EPred $ Pred True  "At" [y]
--                            , EPred $ Pred False "At" [x] ]
--               }

-- testDomain :: Domain
-- testDomain  = [buy,go]

-- testAssumps :: Assumps
-- testAssumps  = [ Pred True "At"    ["Home"]
--                , Pred True "Sells" ["SM","Milk"]
--                , Pred True "Sells" ["SM","Banana"]
--                , Pred True "Sells" ["HW","Drill"]
--                ]

-- testGoals :: Goals
-- testGoals  = [ Pred True "Have" ["Milk"]
--              , Pred True "At" ["Home"]
--              , Pred True "Have" ["Banana"]
--              , Pred True "Have" ["Drill"]
--              ]

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




testDomain =
  [ forall [ "monster", "char", "place" ] $ \ [ monster, char, place ] ->
    Action { aName        = "threaten"
           , aActors      = [ monster ]
           , aHappening   = True
           , aConstraints = [ Pred True "monster"   [ monster ]
                            , Pred True "character" [ char    ]
                            , Pred True "place"     [ place   ]
                            ]
           , aPrecond     = [ PNeq char monster
                            , Pred True "at"    [ monster, place ]
                            , Pred True "at"    [ char,    place ]
                            , Pred True "scary" [ monster        ]
                            ]
           , aEffect      = [ PIntends char (Pred False "alive" [ monster ])
                            ]
           }

  , forall ["char", "monster", "place"] $ \ [ char, monster, place ] ->
    Action { aName        = "slay"
           , aActors      = [ char ]
           , aHappening   = False
           , aConstraints = [ Pred True "character" [ char    ]
                            , Pred True "monster"   [ monster ]
                            , Pred True "place"     [ place   ]
                            ]
           , aPrecond     = [ PNeq char monster
                            , Pred True "at"    [ monster, place ]
                            , Pred True "at"    [ char,    place ]
                            , Pred True "scary" [ monster        ]
                            , Pred True "alive" [ monster        ]
                            , Pred True "alive" [ char           ]
                            ]
           , aEffect      = [ Pred False "alive" [ monster ]
                            ]
           }

  , forall ["char", "place", "newPlace"] $ \ [char, place, newPlace] ->
    Action { aName        = "go"
           , aActors      = [ char ]
           , aHappening   = True
           , aConstraints = [
                            ]
           , aPrecond     = [ PNeq place newPlace
                            , Pred True "at"    [ char, place ]
                            , Pred True "alive" [ char        ]
                            , Pred True "place" [ place ]
                            , Pred True "place" [ newPlace ]
                            ]
           , aEffect      = [ Pred False "at" [ char, place ]
                            , Pred True  "at" [ char, newPlace ]
                            ]
           }
  ]


testAssumps =
  [ Pred True "place"     [ "Forest" ]
  , Pred True "place"     [ "Castle" ]
  , Pred True "place"     [ "Bridge" ]
  , Pred True "character" [ "Knight" ]
  , Pred True "monster"   [ "Dragon" ]
  , Pred True "alive"     [ "Knight" ]
  , Pred True "alive"     [ "Dragon" ]

  , Pred True "at"        [ "Knight", "Forest" ]
  , Pred True "at"        [ "Dragon", "Castle" ]
  , Pred True "scary"     [ "Dragon" ]
  ]

-- XXX swapping the order of these two goals makes it seem like the planner
-- won't terminate
testGoals =
  [ Pred True  "at"    [ "Dragon", "Bridge" ]
  , Pred False "alive" [ "Dragon" ]
  ]

test :: IO ()
test = case ipocl testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"
