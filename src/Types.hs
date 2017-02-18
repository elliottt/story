{-# LANGUAGE RecordWildCards #-}

module Types where

import           Control.Monad (filterM)
import           Data.Array (Array,(!))
import           Data.IORef (IORef,newIORef,readIORef,writeIORef,modifyIORef')
import qualified Data.Text as T
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet


data Atom = Atom !T.Text [T.Text]
            deriving (Eq,Show)

type Facts = IntSet.IntSet
type Goals = IntSet.IntSet
type State = IntSet.IntSet

type FactId = Int

data Fact = Fact { fId :: !FactId

                 , fAtom :: !Atom

                 , fPreCond :: Actions
                   -- ^ Effects that have this fact as a pre-condition

                 , fAdd :: Actions
                   -- ^ Effects that add this fact

                 , fDel :: Actions
                   -- ^ Effects that delete this fact
                 } deriving (Show)

type Actors = IntSet.IntSet

type Actor = Int

data Type = Intentional !Actor
          | Happening
            deriving (Show)

type Actions = IntSet.IntSet

type ActionId = Int

data Action = Action { aId :: !ActionId
                     , aType :: !Type
                     , aPre :: Facts
                     , aAdd :: Facts
                     , aDel :: Facts
                     } deriving (Show)

-- | A mapping of open intent facts, to actors that are currently participating
-- in them.
type Intents = IntMap.IntMap Actors

addIntent :: Actors -> Fact -> Intents -> Intents
addIntent b i = IntMap.insertWith IntSet.union (fId i) b


-- Relaxed Planning Graph ------------------------------------------------------

type Level = Int

data Graph = Graph { gFacts   :: !(Array FactId   FactHeader)
                   , gActions :: !(Array ActionId ActionHeader)
                   }

data FactHeader = FactHeader { fhFact :: !Fact
                             , fhLevel :: !(IORef Level)
                               -- ^ The level this fact was activated at
                             }

data ActionHeader = ActionHeader { ahAction :: !Action
                                 , ahPreConds :: !(IORef Int)
                                   -- ^ The number of preconditions remaining
                                 }

-- | Active this fact in the graph, at the given level. Returns a set of actions
-- that were enabled in the graph when this fact became true.
activateFact :: Graph -> FactId -> Level -> IO Actions
activateFact graph @ Graph { .. } = \ i l ->
  do let FactHeader { fhFact = Fact { .. }, .. } = gFacts ! i
     writeIORef fhLevel l

     active <- filterM (satisfyPrecond graph) (IntSet.toList fPreCond)

     return (IntSet.fromList active)
{-# INLINE activateFact #-}

-- | Mark an action has having one of its preconditions satisfied. Returns True
-- when all of its preconditions are satisfied.
satisfyPrecond :: Graph -> ActionId -> IO Bool
satisfyPrecond Graph { .. } = \ e -> 
  do let ActionHeader { ahAction = Action { .. }, .. } = gActions ! e

     active <- readIORef ahPreConds
     let active' = active - 1
     writeIORef ahPreConds active'

     return $! active' == 0
{-# INLINE satisfyPrecond #-}

actionApplies :: Graph -> State -> ActionId -> Bool
actionApplies Graph { .. } state = \ a ->
  let Action { .. } = ahAction (gActions ! a)
   in aPre `IntSet.isSubsetOf` state
{-# INLINE actionApplies #-}

-- | The add effects of an action.
actionPre :: Graph -> ActionId -> Facts
actionPre Graph { .. } a =
  let Action { .. } = ahAction (gActions ! a)
   in aPre
{-# INLINE actionPre #-}

-- | The add effects of an action.
addEffects :: Graph -> ActionId -> Facts
addEffects Graph { .. } a =
  let Action { .. } = ahAction (gActions ! a)
   in aAdd
{-# INLINE addEffects #-}

-- | The del effects of an action.
delEffects :: Graph -> ActionId -> Facts
delEffects Graph { .. } a =
  let Action { .. } = ahAction (gActions ! a)
   in aDel
{-# INLINE delEffects #-}
