{-# LANGUAGE RecordWildCards #-}

module Types where

import           Data.Array (Array,(!))
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

data Graph = Graph { gFacts   :: !(Array FactId   FactHeader)
                   , gActions :: !(Array ActionId ActionHeader)
                   }

data FactHeader = FactHeader { fhFact :: !Fact
                             }

data ActionHeader = ActionHeader { ahAction :: !Action
                                 }

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
