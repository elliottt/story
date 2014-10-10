{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternSynonyms #-}

module Planner.IPOCL where

import           Planner.Plan
import           Pretty ( PP(pp), pretty )

import qualified Planner.Constraints as C
import           Planner.Debug
import           Planner.Monad
import           Planner.Types

import           Control.Applicative
import           Data.Foldable ( asum )
import           Data.Monoid ( mempty )
import qualified Data.Set as Set
import qualified Data.Traversable as T
import           MonadLib hiding ( forM_ )

import           Debug.Trace


ipocl :: Assumps -> Goals -> PlanM [Step]
ipocl as gs =
  do (p,flaws) <- initialPlan as gs
     p'        <- solveGoals p flaws

     let os = orphans p'
     dbg "orphans" os
     guard (null os)

     -- XXX require that there are no orphans
     return (C.subst (pBindings p') (orderedActions p'))


-- Planning Monad --------------------------------------------------------------

getNode :: Plan -> Step -> PlanM Node
getNode p s =
  case getAction s p of
    Just n  -> return n
    Nothing -> empty

lookupFrame :: Plan -> FrameRef -> PlanM Frame
lookupFrame p ref =
  case getFrame ref p of
    Just frame -> return frame
    Nothing    -> empty

fresh :: Var -> PlanM Term
fresh v = do ix <- freshVar
             return (TVar v { varIndex = ix })

freshInst :: Schema (Effect,Action) -> PlanM (Step,Effect,Action)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     ix <- freshVar
     let (eff,oper) = inst ts a
     return (Inst ix (aName oper) ts, eff, oper)

unify :: C.Unify tm => tm -> tm -> Plan -> PlanM Plan
unify l r p =
  do bs' <- C.unify l r (pBindings p)
     return p { pBindings = bs' }


-- Planner ---------------------------------------------------------------------

-- | Solve a series of goals.
solveGoals :: Plan -> Flaws -> PlanM Plan

solveGoals p (FOpenCond g : flaws) =
  do zonkDbg p "Open Condition" g
     (p',newFlaws) <- discoveryAndResolution (causalPlanning p g)
     dbg "newFlaws" newFlaws

     guard (planConsistent p')
     dbg "consistent" ()

     solveGoals p' (flaws ++ newFlaws)

solveGoals p (FMotivation ref : flaws) =
  do frame <- lookupFrame p ref
     zonkDbg p "Motivation Flaw" frame
     (p',newFlaws) <- discoveryAndResolution (motivationPlanning p ref frame)
     dbg "newFlaws" newFlaws

     guard (planConsistent p')
     dbg "consistent" ()

     solveGoals p' (flaws ++ newFlaws)

solveGoals p (FIntent step ref : flaws) =
  do frame <- lookupFrame p ref
     zonkDbg p "Intent Flaw" (step,fGoal frame)
     (p',newFlaws) <- frameSelection p step ref frame
     dbg "flaws" (newFlaws,flaws)

     guard (planConsistent p')
     dbg "consistent" ()

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

     dbg "intentFlaws" intentFlaws
     dbg "frameFlaws"  frameFlaws

     return (p2, flaws ++ frameFlaws ++ intentFlaws)


-- | Given a step that is new to the plan, try deriving frames of commitment for
-- each goal, and yield motivation flaws when they are created.
--
-- The new motivation flaw represents an opportunity to find a step that
-- motivates the final step of the new frame of commitment.
--
--  * Should intent effects be considered when producing a frame of commitment?
--
discoverFrameFlaws :: Step -> Plan -> PlanM (Plan,Flaws)
discoverFrameFlaws s_add p =
  do node <- getNode p s_add
     let Action { .. } = action node
     guard (not (null aActors))

     -- only consider predicate effects, as there's currently no way to
     -- motivate intent
     dbg "length(effects)" (length aEffect)
     foldr (<|>) noFrame [ tryEffectFrame aActors eff | EPred eff <- aEffect ]
  where
  tryEffectFrame actors eff =
    do dbg "try frame" eff
       let (p',refs) = addFrames (map mkFrame actors) p
       return (p', [ FMotivation ref | ref <- refs ])
    where
    mkFrame a = Frame { fSteps      = Set.empty
                      , fActor      = a
                      , fGoal       = eff
                      , fFinal      = s_add
                      , fMotivation = Nothing
                      }

  addFrames frames plan = T.mapAccumL (flip addFrame) plan frames

  noFrame = do dbg "noFrame" =<< freshVar
               return (p, [])


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
                                asum [ do guard (r /= Finish)
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

  isThreatened act es (Link l g r) =
    l /= act &&
    r /= act &&
    or [ C.unifies (negPred g) e pBindings | EPred e <- es ]



-- Operator Selection ----------------------------------------------------------

operatorSelection :: Plan -> Effect -> PlanM (Bool,Step,Plan,Flaws)
operatorSelection p goal =
  asum [ do (p',res) <- byAssumption p goal
            return (False,res,p',mempty)

       , do (s_add,p',flaws) <- byNewStep p goal
            return (True,s_add,p',flaws)

       ,    dbg "whoops" () >> empty
       ]


-- | Resolve an open condition by reusing an exising step in the plan.
byAssumption :: Plan -> Effect -> PlanM (Plan,Step)
byAssumption p goal = asum (map tryAssump (getActions p))
  where
  tryAssump (act,node) =
    do p' <- asum [ dbg "trying" (pp q) >> unify goal q p | q <- effects node ]
       zonkDbg p' "existing" act
       return (p',act)


-- | Resolve an open condition by adding a new step to the plan.
byNewStep :: Plan -> Effect -> PlanM (Step,Plan,Flaws)
byNewStep p goal =
  do actions <- findAction goal
     asum (map tryInst actions)
  where
  tryInst s =
    do dbg "new" ()
       (act,eff,op) <- freshInst s

       -- find an effect that matches the goal
       p1 <- unify eff goal p
       zonkDbg p1 "Effect" eff

       (p2,flaws) <- addAction act op $ (Start `isBefore` act)
                                      $ (act   `isBefore` Finish)
                                        p1

       return (act,p2,flaws)


-- Causal Planning -------------------------------------------------------------

causalPlanning :: Plan -> Goal -> PlanM (Bool,Step,Plan,Flaws)
causalPlanning p Goal { .. } =
  do (isNew,s_add,p1,flaws) <- operatorSelection p (EPred gGoal)

     let p2 = (s_add `isBefore` gSource)
            $ addLink (Link s_add gGoal gSource)
              p1

     return (isNew,s_add,p2,flaws)


-- Motivation Planning ---------------------------------------------------------

-- | A frame of commitment that currently lacks a motivating step.
motivationPlanning :: Plan -> FrameRef -> Frame -> PlanM (Bool,Step,Plan,Flaws)
motivationPlanning p ref c @ Frame { .. } =
  do let goal = EIntends fActor fGoal

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
  asum [ do motivation <- case fMotivation frame of
                            Just s  -> return s
                            Nothing -> empty

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
  addStep f = f { fSteps = Set.insert step (fSteps frame) }
