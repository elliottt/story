{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}

module Plan where

import FloydWarshall ( transitiveClosure )
import Pretty

import           Planner.Constraints as C
import           Planner.Monad
import           Planner.Types

import           Control.Monad ( foldM )
import           Data.Array.IArray ( (!) )
import qualified Data.Foldable as F
import qualified Data.Graph as Graph
import qualified Data.Graph.SCC as SCC
import           Data.List ( sortBy )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set


-- Types -----------------------------------------------------------------------

type FrameRef = Int

data Plan = Plan { pBindings :: BindConsts
                   -- ^ Current set of variable bindings
                 , pNodes    :: Map.Map Step Node
                   -- ^ Instantiated actions, and their dependencies
                 , pLinks    :: Set.Set Link
                   -- ^ Causal links
                 , pFrames   :: Map.Map FrameRef Frame
                   -- ^ Frames of commitment
                 } deriving (Show)

data Node = Node { nodeInst     :: Action
                   -- ^ The instantiated operator
                 , nodeBefore   :: Set.Set Step
                   -- ^ Nodes that come before this one in the graph
                 , nodeAfter    :: Set.Set Step
                 } deriving (Show)

-- | An open condition flaw.
data Goal = Goal { gSource  :: Step
                 , gGoal    :: Pred
                 } deriving (Show,Eq,Ord)

type Flaws = [Flaw]

data Flaw = FOpenCond Goal
          | FMotivation FrameRef
          | FIntent Step FrameRef
            deriving (Show)


-- PlanState Operations --------------------------------------------------------

planConsistent :: Plan -> Bool
planConsistent p = ordsConsistent p && C.consistent (pBindings p)

-- | Form a plan state from an initial set of assumptions, and goals.
initialPlan :: Assumps -> Goals -> PlanM (Plan,Flaws)
initialPlan as gs =
  do (psStart,_)      <- addAction Start emptyAction { aName   = "<Start>"
                                                     , aEffect = map EPred as
                                                     } emptyPlan

     (psFinish,flaws) <- addAction Finish emptyAction { aName     = "<Finish>"
                                                      , aPrecond  = gs
                                                      } psStart

     return ((Start `isBefore` Finish) psFinish, flaws)
  where
  emptyPlan        = Plan { pBindings = C.empty
                          , pNodes    = Map.empty
                          , pLinks    = Set.empty
                          , pFrames   = Map.empty
                          }


-- | Retrieve variable bindings from the plan.
getBindings :: Plan -> BindConsts
getBindings  = pBindings

-- | Set variable bindings in the plan.
setBindings :: BindConsts -> Plan -> Plan
setBindings env p = p { pBindings = env }

getActions :: Plan -> [(Step,Node)]
getActions Plan { .. } = Map.toList pNodes

getAction :: Step -> Plan -> Maybe Node
getAction step Plan { .. } = Map.lookup step pNodes

addFrame :: Frame -> Plan -> (Plan,FrameRef)
addFrame frame p = (p',key)
  where
  key = case Map.maxViewWithKey (pFrames p) of
          Just ((k,_), _) -> k + 1
          Nothing         -> 0

  p' = p { pFrames = Map.insert key frame (pFrames p) }

modifyFrame :: FrameRef -> (Frame -> Frame) -> Plan -> Plan
modifyFrame ref f ps = ps { pFrames = Map.adjust f ref (pFrames ps) }

getFrame :: FrameRef -> Plan -> Maybe Frame
getFrame ref Plan { .. } = Map.lookup ref pFrames

-- | Modify an existing action.
modifyAction :: Step -> (Node -> Node) -> (Plan -> Plan)
modifyAction act f ps = ps { pNodes = Map.adjust f act (pNodes ps) }

-- | Add an action, with its instantiation, to the plan state.  All
-- preconditions of the action will be considered goals, and appended to the
-- agenda.
addAction :: Step -> Action -> Plan -> PlanM (Plan,Flaws)
addAction act oper p =
  do bs' <- foldM (flip constrain) (pBindings p') (aConstraints oper)
     return (p' { pBindings = bs' },newGoals)
  where
  p' = p { pNodes = Map.insert act Node { nodeInst     = oper
                                        , nodeBefore   = Set.empty
                                        , nodeAfter    = Set.empty
                                        } (pNodes p) }

  newGoals = [ FOpenCond (Goal act tm) | tm <- aPrecond oper ]

-- | Record that action a comes before action b, in the plan state.
isBefore :: Step -> Step -> Plan -> Plan
a `isBefore` b = modifyAction b (addBefore a)
               . modifyAction a (addAfter  b)

isBeforeFrame :: Step -> Frame -> Plan -> Plan
a `isBeforeFrame` c = foldl (.) id orderings
  where
  orderings = [ a `isBefore` step | step <- Set.toList (allSteps c) ]

addLink :: Link -> Plan -> Plan
addLink l p = p { pLinks = Set.insert l (pLinks p) }

getLinks :: Plan -> Set.Set Link
getLinks  = pLinks

-- | Check that there are no cycles in the graph.
ordsConsistent :: Plan -> Bool
ordsConsistent ps = all isAcyclic (scc ps)
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic _                  = False

scc :: Plan -> [Graph.SCC (Step,Node)]
scc Plan { .. } = SCC.stronglyConnComp
  [ ((key,node), key, es) | (key,node) <- Map.toList pNodes
                          , let es = Set.toList (nodeAfter node) ]

-- | Turn the plan state into a graph, and create a function for recovering
-- information about the actions in the plan.
actionGraph :: Plan
            -> (Node -> Set.Set Step)
            -> ( Graph.Graph
               , Graph.Vertex -> (Step,Node)
               , Step -> Maybe Graph.Vertex )
actionGraph Plan { .. } prj = (graph, lookupAction, toVertex)
  where
  (graph, fromVertex, toVertex) = Graph.graphFromEdges
    [ ((key,node), key, es) | (key,node) <- Map.toList pNodes
                            , let es = Set.toList (prj node) ]

  lookupAction v = case fromVertex v of
                     (x,_,_) -> x

-- | Produce a linear plan from a plan state.
orderedActions :: Plan -> [Step]
orderedActions ps = [ act | vert <- sorted
                          , let (act,_) = fromVertex vert ]
  where
  (graph,fromVertex,_) = actionGraph ps nodeAfter

  relation                      = transitiveClosure graph
  ordRel a b | a == b           = EQ
             | relation ! (a,b) = LT
             | otherwise        = GT

  sorted               = sortBy ordRel (Graph.vertices graph)


-- Frame Operations ------------------------------------------------------------

-- | Gather up frames of commitment that are related by the same character
-- intent.
sameIntent :: Step -> Plan -> Set.Set FrameRef
sameIntent s_add p
  | Just node <- getAction s_add p = relatedBy (nodeInst node)
  | otherwise                      = Set.empty
  where
  relatedBy act =
    Set.fromList [ k | (k,f) <- Map.toList (pFrames p)
                     , let steps = Set.intersection interactingSteps (allSteps f)
                     , not (Set.null steps)
                     , F.all sameActors steps ]
    where

    interactsWithNew Link { .. } = clLeft == s_add

    interactingSteps = Set.map clRight (Set.filter interactsWithNew (pLinks p))

    -- any overlap between actors is acceptable.
    sameActors sid

      | Just Node { nodeInst = act' } <- getAction sid p
      , not (null (aActors act')) =
        or [ equivalent a b (pBindings p) | TVar a <- aActors act
                                          , TVar b <- aActors act' ]

      | otherwise =
        False



-- Node Operations -------------------------------------------------------------

addAfter :: Step -> Node -> Node
addAfter act node = node { nodeAfter = Set.insert act (nodeAfter node) }

addBefore :: Step -> Node -> Node
addBefore act node = node { nodeBefore = Set.insert act (nodeBefore node) }

effects :: Node -> [Effect]
effects Node { .. } = aEffect nodeInst

action :: Node -> Action
action Node { .. } = nodeInst


-- Utility Instances -----------------------------------------------------------

instance PP Goal where
  pp Goal { .. } = hang (pp gGoal)
                      2 (text "from" <+> pp gSource)
