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
ipocl d as gs = runPlanM as d $
  do p' <- solveGoals p flaws
     -- XXX require that there are no orphans
     zonk p' (orderedActions p')
  where
  (p,flaws) = initialPlan as gs


-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Applicative,Monad,Alternative
                                   ,MonadPlus)

data RW = RW { rwFresh  :: Int
             , rwDomain :: T.Domain
             , rwFacts  :: T.Facts
               -- ^ Static knowledge from the initial state
             } deriving (Show)

runPlanM :: Assumps -> Domain -> PlanM a -> Maybe a
runPlanM as d m =
  case runId (findOne (runStateT rw (unPlanM m))) of
    Just (a,_) -> Just a
    Nothing    -> Nothing
  where
  rw = RW { rwFresh  = 0
          , rwDomain = T.mkDomain d
          , rwFacts  = T.mkFacts as
          }

getFacts :: PlanM T.Facts
getFacts  = PlanM $ do RW { .. } <- get
                       return rwFacts

nextId :: PlanM Int
nextId  = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (rwFresh rw)

getNode :: Plan -> Step -> PlanM Node
getNode p s =
  case getAction s p of
    Just n  -> return n
    Nothing -> mzero

lookupFrame :: Plan -> FrameRef -> PlanM Frame
lookupFrame p ref =
  case getFrame ref p of
    Just frame -> return frame
    Nothing    -> mzero

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

-- XXX extending the binding environment might invalidate the causal links.
-- What's the best way to detect this?
match :: Unify.Unify tm => tm -> tm -> Plan -> PlanM Plan
match l r p =
  case Unify.match (pBindings p) l r of
    Right bs' -> return p { pBindings = bs' }
    Left _    -> mzero

unify :: (Unify.Unify tm, PP tm) => tm -> tm -> Plan -> PlanM Plan
unify l r p =
  case Unify.mgu (pBindings p) l r of
    Right bs' -> return p { pBindings = bs' }
    Left _    -> mzero

zonk :: Unify.Zonk tm => Plan -> tm -> PlanM tm
zonk Plan { .. } tm =
  case Unify.zonk pBindings tm of
    Right tm' -> return tm'
    Left _    -> mzero

dbg :: Show a => String -> a -> PlanM ()
dbg l a = traceM (l ++ ": " ++ show a)

zonkDbg :: (PP a, Unify.Zonk a) => Plan -> String -> a -> PlanM ()
zonkDbg p l a = do a' <- zonk p a
                   traceM (show (hang (text l <> char ':') 2 (pp a')))


-- Planner ---------------------------------------------------------------------

-- | Solve a series of goals.
solveGoals :: Plan -> Flaws -> PlanM Plan

solveGoals p (FOpenCond g : flaws) =
  do zonkDbg p "Open Condition" g
     (p',newFlaws) <- discoveryAndResolution (causalPlanning p g)
     dbg "newFlaws" (null newFlaws)
     solveGoals p' (flaws ++ newFlaws)

solveGoals p (FMotivation ref : flaws) =
  do frame <- lookupFrame p ref
     zonkDbg p "Motivation Flaw" frame
     (p',newFlaws) <- discoveryAndResolution (motivationPlanning p ref frame)
     dbg "newFlaws" newFlaws
     solveGoals p' (flaws ++ newFlaws)

solveGoals p (FIntent step ref : flaws) =
  do frame <- lookupFrame p ref
     zonkDbg p "Intent Flaw" (step,fGoal frame)
     (p',newFlaws) <- frameSelection p step ref frame
     dbg "flaws" (newFlaws,flaws)
     solveGoals p' (flaws ++ newFlaws)

solveGoals p [] =
  do dbg "DONE" ()
     return p


-- Threat Resolution -----------------------------------------------------------

discoveryAndResolution :: PlanM (Bool,Step,Plan,Flaws) -> PlanM (Plan,Flaws)
discoveryAndResolution body =
  do (isNew,s_add,p,flaws) <- body

     zonkDbg p "s_add" s_add

     (p1,frameFlaws) <- if isNew
                           then discoverFrameFlaws s_add p
                           else return (p,mempty)

     intentFlaws <- discoverIntentFlaws s_add p1

     p2 <- resolveCausalThreats p1

     guard (planConsistent p2)

     dbg "consistent" ()
     dbg "intentFlaws" intentFlaws

     return (p2, flaws ++ frameFlaws ++ intentFlaws)


-- | Given a step that is new to the plan, derive frames of commitment for each
-- goal, and yield motivation flaws.
--
-- The new motivation flaw represents an opportunity to find a step that
-- motivates the final step of the new frame of commitment.
--
--  * Should intent effects be considered when producing a frame of commitment?
--
discoverFrameFlaws :: Step -> Plan -> PlanM (Plan,Flaws)
discoverFrameFlaws s_add p = discoverEffectFrame `mplus` noFrame
  where
  discoverEffectFrame =
    do node <- getNode p s_add
       let Action { .. } = action node
       guard (not (null aActors))
       msum [ tryEffectFrame aActors eff | eff <- aEffect ]

  tryEffectFrame actors eff =
    do let (p',refs) = addFrames (map mkFrame actors) p
       return (p', [ FMotivation ref | ref <- refs ])
    where
    mkFrame a = Frame { fSteps      = Set.empty
                      , fActor      = a
                      , fGoal       = eff
                      , fFinal      = s_add
                      , fMotivation = Nothing
                      }

  addFrames frames plan = T.mapAccumL (flip addFrame) plan frames

  noFrame = return (p, [])


-- | Find all frames of commitment that could be used to explain s_add, and for
-- each one, emit an intent flaw.
discoverIntentFlaws :: Step -> Plan -> PlanM Flaws
discoverIntentFlaws s_add p =
  do -- first, find all frames that have a step that has an effect of s_add as a
     -- precondition
     let cond1 = sameIntent s_add p

     -- XXX cond1 only represents half of the picture when generating intent
     -- flaws

     -- generate intent flaws
     return [ FIntent s_add ref | ref <- Set.toList cond1 ]


resolveCausalThreats :: Plan -> PlanM Plan
resolveCausalThreats p
  | null threats = return p
  | otherwise    = do funs <- forM threats $ \ (act,Link l _ r) ->
                                msum [ do guard (r /= Finish)
                                          return (r `isBefore` act)
                                     , do guard (l /= Start)
                                          return (act `isBefore` l)
                                     ]
                      return (foldr ($) p funs)
  where
  threats = causalThreats p

-- | Discover causal threats in the plan.
causalThreats :: Plan -> [(Step,Link)]
causalThreats p @ Plan { .. } =
  [ (act,link) | (act,node) <- as
               , link       <- Set.toList links
               , isThreatened act (effects node) link ]
  where
  as    = getActions p
  links = getLinks p

  unifies p q = case Unify.mgu pBindings p q of
                  Right {} -> True
                  Left {}  -> False

  isThreatened act es (Link l p r) =
    l /= act &&
    r /= act &&
    any (unifies (negPred p)) es



-- Operator Selection ----------------------------------------------------------

operatorSelection :: Plan -> Pred -> PlanM (Bool,Step,Plan,Flaws)
operatorSelection p goal =
  msum [ do (p',res) <- byAssumption p goal
            return (False,res,p',mempty)
       , do (s_add,p',flaws) <- byNewStep p goal
            return (True,s_add,p',flaws)
       ]


-- | Resolve an open condition by reusing an exising step in the plan.
byAssumption :: Plan -> Pred -> PlanM (Plan,Step)
byAssumption p goal = msum (map tryAssump (getActions p))
  where
  tryAssump (act,node) =
    do p' <- msum [ unify goal q p | q <- effects node ]
       zonkDbg p' "existing" act
       return (p',act)


-- | Resolve an open condition by adding a new step to the plan.
byNewStep :: Plan -> Pred -> PlanM (Step,Plan,Flaws)
byNewStep p goal =
  do dom <- getDomain
     msum (map tryInst (T.lookup goal dom))
  where
  tryInst s =
    do dbg "new" ()
       (act,op) <- freshInst s

       -- find an effect that matches the goal
       bs' <- case mapMaybe isRelevant (aEffect op) of
                env' : _ -> return env'
                []       -> mzero

       let (p1,ns,flaws) = addAction act op
                         $ (Start `isBefore` act)
                         $ (act   `isBefore` Finish)
                           p

       dbg "before" ()
       dbg "ns" ns
       p2 <- case Unify.neqs (pBindings p1) ns of
               Right bs -> return p1 { pBindings = bs }
               Left _   -> mzero

       -- when constraints exist, examine the facts to variable binding choices
       p3 <- useConstraints act (aConstraints op) p2

       return (act,p2,flaws)

  isRelevant q =
    case Unify.mgu (pBindings p) goal q of
      Right env' -> Just env'
      Left _     -> Nothing


useConstraints :: Step -> [Pred] -> Plan -> PlanM Plan
useConstraints from cs p0 =
  do facts <- getFacts
     loop facts cs p0
  where
  loop facts (c:cs) p = msum [ do p' <- unify c atom p
                                  loop facts cs p'
                             | atom <- T.lookup c facts ]
  loop _     []     p = return p


-- Causal Planning -------------------------------------------------------------

causalPlanning :: Plan -> Goal -> PlanM (Bool,Step,Plan,Flaws)
causalPlanning p Goal { .. } =
  do (isNew,s_add,p1,flaws) <- operatorSelection p gGoal

     let p2 = (s_add `isBefore` gSource)
            $ addLink (Link s_add gGoal gSource)
              p1

     return (isNew,s_add,p2,flaws)


-- Motivation Planning ---------------------------------------------------------

-- | A frame of commitment that currently lacks a motivating step.
motivationPlanning :: Plan -> FrameRef -> Frame -> PlanM (Bool,Step,Plan,Flaws)
motivationPlanning p ref c @ Frame { .. } =
  do let goal = PIntends fActor fGoal

     (isNew,s_add,p1,flaws) <- operatorSelection p goal

     let link = Link s_add fGoal fFinal

     let p2 = (s_add `isBeforeFrame` c)
            $ addLink link
            $ modifyFrame ref (\ f -> f { fMotivation = Just s_add })
              p1

     return (isNew,s_add,p2,flaws)


-- Intent Planning -------------------------------------------------------------

frameSelection :: Plan -> Step -> FrameRef -> Frame -> PlanM (Plan,Flaws)
frameSelection p step ref frame =
  msum [ do motivation <- case fMotivation frame of
                            Just s  -> return s
                            Nothing -> mzero

            -- add the step to the frame, and order it after the motivating
            -- step
            let p' = modifyFrame ref addStep
                   $ (motivation `isBefore` step) p

            -- XXX order frames WRT each other

            -- XXX generate intent flaws for causal links with the same
            -- character that occur before the new step

            return (p',[])

       ,    return (p,[])
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
           , aConstraints = [ {- Pred True "monster"   [ monster ]
                            , Pred True "character" [ char    ]
                            , Pred True "place"     [ place   ] -}
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
           , aConstraints = [ {- Pred True "character" [ char    ]
                            , Pred True "monster"   [ monster ]
                            , Pred True "place"     [ place   ] -}
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
                            ]
           , aEffect      = [ Pred False "at" [ char, place ]
                            , Pred True  "at" [ char, newPlace ]
                            ]
           }
  ]


testAssumps =
  [ Pred True "place"     [ "Castle" ]
  , Pred True "place"     [ "Castle" ]
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
  [ Pred False "alive" [ "Dragon" ]
  ]

test :: IO ()
test = case ipocl testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"
