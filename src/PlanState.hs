{-# LANGUAGE RecordWildCards #-}

module PlanState where

import Unify ( Env )
import Types

import qualified Data.Graph as Graph
import qualified Data.Graph.SCC as SCC
import qualified Data.IntSet as IntSet
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, fromJust )
import qualified Data.Set as Set
import qualified Data.Tree as Tree


-- Types -----------------------------------------------------------------------

data PlanState = PlanState { psBindings :: Env
                           , psNodes    :: Map.Map Action Node
                           } deriving (Show)

data Node = Node { nodeInst     :: Operator
                   -- ^ The instantiated operator
                 , nodeBefore   :: Set.Set Action
                   -- ^ Nodes that come before this one in the graph
                 , nodeAfter    :: Set.Set Action
                   -- ^ Nodes that come after this one in the graph
                 , nodeProtects :: Set.Set (Pred,Action)
                   -- ^ Causal links between this node and others
                 } deriving (Show)

data Goal = Goal { gSource :: Action
                 , gPred   :: Pred
                 } deriving (Show)


-- PlanState Operations --------------------------------------------------------

-- | Form a plan state from an initial set of assumptions, and goals.
initialPlanState :: Assumps -> Goals -> (PlanState,[Goal])
initialPlanState as gs = ((Start `before` Finish) psFinish, goals)
  where
  emptyPlan        = PlanState { psBindings = Map.empty
                               , psNodes    = Map.empty
                               }

  (psStart,_)      = addAction Start  Operator { oName     = "<Start>"
                                               , oPrecond  = []
                                               , oPostcond = as } emptyPlan

  (psFinish,goals) = addAction Finish Operator { oName     = "<Finish>"
                                               , oPrecond  = gs
                                               , oPostcond = [] } psStart

-- | Modify an existing action.
modifyAction :: Action -> (Node -> Node) -> (PlanState -> PlanState)
modifyAction act f ps = ps { psNodes = Map.adjust f act (psNodes ps) }

-- | Add an action, with its instantiation, to the plan state.  All
-- preconditions of the goal will be considered goals, and appended to the
-- agenda.
addAction :: Action -> Operator -> PlanState -> (PlanState,[Goal])
addAction act oper ps = (ps',newGoals)
  where
  ps' = ps { psNodes = Map.insert act Node { nodeInst     = oper
                                           , nodeBefore   = Set.empty
                                           , nodeAfter    = Set.empty
                                           , nodeProtects = Set.empty
                                           } (psNodes ps)
           }
  newGoals = [ Goal act p | p <- oPrecond oper ]

-- | Record that action a comes before action b, in the plan state.
before :: Action -> Action -> PlanState -> PlanState
a `before` b = modifyAction b (addBefore a)
             . modifyAction a (addAfter  b)

addLink :: Action -> Pred -> Action -> PlanState -> PlanState
addLink l p r = modifyAction l $ \ node ->
  node { nodeProtects = Set.insert (p,r) (nodeProtects node) }

-- | All actions that occur on the given interval.
between :: Action -> Action -> PlanState -> [(Action,Node)]
between l r ps = [ fromVertex v | v <- fromR, v `IntSet.member` pre ]
  where

  -- build the forward and backward views of the graph
  (graph, fromVertex, toVertex) = actionGraph ps
  backwards                     = Graph.transposeG graph

  -- default the bounds to Start/Finish respectively
  lv = fromMaybe (fromJust (toVertex Start))  (toVertex l)
  rv = fromMaybe (fromJust (toVertex Finish)) (toVertex r)

  -- reachable nodes from the left/right bounds
  fromL = concatMap Tree.flatten (Graph.dfs graph     [lv])
  fromR = concatMap Tree.flatten (Graph.dfs backwards [rv])

  pre = IntSet.fromList fromL IntSet.\\ IntSet.fromList [lv,rv]

-- | Check that there are no cycles in the graph.
ordsConsistent :: PlanState -> Bool
ordsConsistent ps = all isAcyclic (scc ps)
  where
  isAcyclic Graph.AcyclicSCC{} = True
  isAcyclic _                  = False

scc :: PlanState -> [Graph.SCC (Action,Node)]
scc PlanState { .. } = SCC.stronglyConnComp
  [ ((key,node), key, es) | (key,node) <- Map.toList psNodes
                          , let es = Set.toList (nodeAfter node) ]

-- | Turn the plan state into a graph, and create a function for recovering
-- information about the actions in the plan.
actionGraph :: PlanState -> ( Graph.Graph
                            , Graph.Vertex -> (Action,Node)
                            , Action -> Maybe Graph.Vertex )
actionGraph PlanState { .. } = (graph, getAction, toVertex)
  where
  (graph, fromVertex, toVertex) = Graph.graphFromEdges
    [ ((key,node), key, es) | (key,node) <- Map.toList psNodes
                            , let es = Set.toList (nodeAfter node) ]

  getAction v = case fromVertex v of
                  (x,_,_) -> x

-- | Produce a linear plan from a plan state.
orderedActions :: PlanState -> [Action]
orderedActions ps = [ act | vert <- Graph.topSort graph
                          , let (act,_) = fromVertex vert ]
  where
  (graph,fromVertex,_) = actionGraph ps


-- Node Operations -------------------------------------------------------------

addAfter :: Action -> Node -> Node
addAfter act node = node { nodeAfter = Set.insert act (nodeAfter node) }

addBefore :: Action -> Node -> Node
addBefore act node = node { nodeBefore = Set.insert act (nodeBefore node) }
