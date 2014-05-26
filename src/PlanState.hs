{-# LANGUAGE RecordWildCards #-}

module PlanState (
    -- * Partial Plans
    Plan()
  , initialPlan
  , addAction
  , zonkPlan
  , getActions
  , planConsistent

    -- ** Variable Bindings
  , getBindings
  , setBindings

    -- ** Ordering Constraints
  , isBefore
  , orderedActions

    -- ** Causal Links
  , addLink
  , getLinks

    -- ** Graph Nodes
  , Node()
  , effects

    -- * Goals
  , Goal(..)
  ) where

import FloydWarshall ( transitiveClosure )
import Pretty
import Unify ( Error, Env, Zonk(..), zonk )
import Types

import           Control.Applicative ( (<$>), (<*>) )
import           Data.Array.IArray ( (!) )
import qualified Data.Graph as Graph
import qualified Data.Graph.SCC as SCC
import           Data.List ( sortBy )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set


-- Types -----------------------------------------------------------------------

data Plan = Plan { pBindings :: Env
                   -- ^ Current set of variable bindings
                 , pNodes    :: Map.Map Action Node
                   -- ^ Instantiated actions, and their dependencies
                 , pLinks    :: Set.Set Link
                   -- ^ Causal links
                 } deriving (Show)

data Node = Node { nodeInst     :: Operator
                   -- ^ The instantiated operator
                 , nodeBefore   :: Set.Set Action
                   -- ^ Nodes that come before this one in the graph
                 , nodeAfter    :: Set.Set Action
                   -- ^ Nodes that come after this one in the graph
                 } deriving (Show)

data Goal = Goal { gSource  :: Action
                 , gPred    :: Pred
                 , gEffects :: [Pred]
                 } deriving (Show)


-- PlanState Operations --------------------------------------------------------

zonkPlan :: Plan -> Either Error Plan
zonkPlan plan = case zonk (pBindings plan) (pNodes plan) of
  Right nodes' -> Right plan { pNodes = nodes' }
  Left err     -> Left err

planConsistent :: Plan -> Bool
planConsistent  = ordsConsistent

-- | Form a plan state from an initial set of assumptions, and goals.
initialPlan :: Assumps -> Goals -> (Plan,[Goal])
initialPlan as gs = ((Start `isBefore` Finish) psFinish, goals)
  where
  emptyPlan        = Plan { pBindings = Map.empty
                          , pNodes    = Map.empty
                          , pLinks    = Set.empty
                          }

  (psStart,_)      = addAction Start  Operator { oName     = "<Start>"
                                               , oPrecond  = []
                                               , oPostcond = as } emptyPlan

  (psFinish,goals) = addAction Finish Operator { oName     = "<Finish>"
                                               , oPrecond  = gs
                                               , oPostcond = [] } psStart
-- | Retrieve variable bindings from the plan.
getBindings :: Plan -> Env
getBindings  = pBindings

-- | Set variable bindings in the plan.
setBindings :: Env -> Plan -> Plan
setBindings env p = p { pBindings = env }


getActions :: Plan -> [(Action,Node)]
getActions Plan { .. } = Map.toList pNodes

-- | Modify an existing action.
modifyAction :: Action -> (Node -> Node) -> (Plan -> Plan)
modifyAction act f ps = ps { pNodes = Map.adjust f act (pNodes ps) }

-- | Add an action, with its instantiation, to the plan state.  All
-- preconditions of the goal will be considered goals, and appended to the
-- agenda.
addAction :: Action -> Operator -> Plan -> (Plan,[Goal])
addAction act oper p = (p',newGoals)
  where
  p' = p { pNodes = Map.insert act Node { nodeInst     = oper
                                        , nodeBefore   = Set.empty
                                        , nodeAfter    = Set.empty
                                        } (pNodes p) }
  newGoals = [ Goal act tm (oPostcond oper) | tm <- oPrecond oper ]

-- | Record that action a comes before action b, in the plan state.
isBefore :: Action -> Action -> Plan -> Plan
a `isBefore` b = modifyAction b (addBefore a)
               . modifyAction a (addAfter  b)

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

scc :: Plan -> [Graph.SCC (Action,Node)]
scc Plan { .. } = SCC.stronglyConnComp
  [ ((key,node), key, es) | (key,node) <- Map.toList pNodes
                          , let es = Set.toList (nodeAfter node) ]

-- | Turn the plan state into a graph, and create a function for recovering
-- information about the actions in the plan.
actionGraph :: Plan
            -> (Node -> Set.Set Action)
            -> ( Graph.Graph
               , Graph.Vertex -> (Action,Node)
               , Action -> Maybe Graph.Vertex )
actionGraph Plan { .. } prj = (graph, getAction, toVertex)
  where
  (graph, fromVertex, toVertex) = Graph.graphFromEdges
    [ ((key,node), key, es) | (key,node) <- Map.toList pNodes
                            , let es = Set.toList (prj node) ]

  getAction v = case fromVertex v of
                  (x,_,_) -> x

-- | Produce a linear plan from a plan state.
orderedActions :: Plan -> [Action]
orderedActions ps = [ act | vert <- sorted
                          , let (act,_) = fromVertex vert ]
  where
  (graph,fromVertex,_) = actionGraph ps nodeAfter

  relation                      = transitiveClosure graph
  ordRel a b | a == b           = EQ
             | relation ! (a,b) = LT
             | otherwise        = GT

  sorted               = sortBy ordRel (Graph.vertices graph)


-- Node Operations -------------------------------------------------------------

addAfter :: Action -> Node -> Node
addAfter act node = node { nodeAfter = Set.insert act (nodeAfter node) }

addBefore :: Action -> Node -> Node
addBefore act node = node { nodeBefore = Set.insert act (nodeBefore node) }

effects :: Node -> [Pred]
effects Node { .. } = oPostcond nodeInst


-- Utility Instances -----------------------------------------------------------

instance Zonk Node where
  zonk' Node { .. } = Node <$> zonk' nodeInst
                           <*> zonk' nodeBefore
                           <*> zonk' nodeAfter

instance Zonk Goal where
  zonk' Goal { .. } = Goal <$> zonk' gSource
                           <*> zonk' gPred
                           <*> zonk' gEffects

instance PP Goal where
  pp Goal { .. } = pp gPred <+> text "from" <+> pp gSource
