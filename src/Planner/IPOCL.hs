{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternSynonyms #-}

module Planner.IPOCL where

import           Pretty ( PP(pp), (<>), hang, text, char )
import           Plan
import qualified Unify

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
  do p' <- solveGoals p flaws
     -- XXX require that there are no orphans
     zonk p' (orderedActions p')
  where
  (p,flaws) = initialPlan as gs


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

freshInst :: Schema (Pred,Action) -> PlanM (Step,Pred,Action)
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     ix <- freshVar
     let (eff,oper) = inst ts a
     return (Inst ix (aName oper) ts, eff, oper)

-- XXX extending the binding environment might invalidate the causal links.
-- What's the best way to detect this?
match :: Unify.Unify tm => tm -> tm -> Plan -> PlanM Plan
match l r p =
  case Unify.match (pBindings p) l r of
    Right bs' -> return p { pBindings = bs' }
    Left _    -> empty

unify :: (Unify.Unify tm, PP tm) => tm -> tm -> Plan -> PlanM Plan
unify l r p =
  case Unify.mgu (pBindings p) l r of
    Right bs' -> return p { pBindings = bs' }
    Left _    -> empty

zonk :: Unify.Zonk tm => Plan -> tm -> PlanM tm
zonk Plan { .. } tm =
  case Unify.zonk pBindings tm of
    Right tm' -> return tm'
    Left _    -> empty

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
       asum [ tryEffectFrame aActors eff | eff <- aEffect ]

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

  unifies x y = case Unify.mgu pBindings x y of
                  Right {} -> True
                  Left {}  -> False

  isThreatened act es (Link l g r) =
    l /= act &&
    r /= act &&
    any (unifies (negPred g)) es



-- Operator Selection ----------------------------------------------------------

operatorSelection :: Plan -> Pred -> PlanM (Bool,Step,Plan,Flaws)
operatorSelection p goal =
  asum [ do (p',res) <- byAssumption p goal
            return (False,res,p',mempty)
       , do (s_add,p',flaws) <- byNewStep p goal
            return (True,s_add,p',flaws)
       ]


-- | Resolve an open condition by reusing an exising step in the plan.
byAssumption :: Plan -> Pred -> PlanM (Plan,Step)
byAssumption p goal = asum (map tryAssump (getActions p))
  where
  tryAssump (act,node) =
    do p' <- asum [ unify goal q p | q <- effects node ]
       zonkDbg p' "existing" act
       return (p',act)


-- | Resolve an open condition by adding a new step to the plan.
byNewStep :: Plan -> Pred -> PlanM (Step,Plan,Flaws)
byNewStep p goal =
  do actions <- findAction goal
     asum (map tryInst actions)
  where
  tryInst s =
    do dbg "new" ()
       (act,eff,op) <- freshInst s

       -- find an effect that matches the goal
       p1 <- unify eff goal p

       let (p2,ns,flaws) = addAction act op
                         $ (Start `isBefore` act)
                         $ (act   `isBefore` Finish)
                           p

       dbg "before" ()
       dbg "ns" ns
       p3 <- case Unify.neqs (pBindings p2) ns of
               Right bs -> return p1 { pBindings = bs }
               Left _   -> empty

       -- when constraints exist, examine the facts to variable binding choices
       --p4 <- useConstraints act (aConstraints op) p3

       return (act,p3,flaws)


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
