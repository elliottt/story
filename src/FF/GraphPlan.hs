{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module FF.GraphPlan where

import           Control.Monad ( unless )
import           Data.Array
import           Data.IORef ( IORef, newIORef, writeIORef, readIORef )
import qualified Data.IntSet as IS
import           Data.Monoid ( Monoid(..) )
import           Data.Word ( Word32 )


-- Predicates ------------------------------------------------------------------

-- | Ground, positive predicates.
data Pred = Pred String [String]
            deriving (Show,Eq,Ord)


-- Reference Sets --------------------------------------------------------------

newtype RefSet a = RefSet IS.IntSet
                   deriving (Show,Eq,Monoid)

class Ref a where
  toRef   :: Int -> a
  fromRef :: a -> Int

instance Ref FactRef where
  toRef               = FactRef
  fromRef (FactRef r) = r

instance Ref EffectRef where
  toRef                 = EffectRef
  fromRef (EffectRef r) = r

refs :: Ref a => RefSet a -> [a]
refs (RefSet is) = [ toRef r | r <- IS.toList is ]

isNull :: RefSet a -> Bool
isNull (RefSet rs) = IS.null rs

singleton :: Ref a => a -> RefSet a
singleton a = RefSet (IS.singleton (fromRef a))


-- Connection Graph ------------------------------------------------------------

data ConnGraph = ConnGraph { cgFacts   :: !(Array FactRef Fact)
                           , cgOpers   :: !(Array OperRef Oper)
                           , cgEffects :: !(Array EffectRef Effect)
                           }

newtype FactRef = FactRef Int
                  deriving (Show,Eq,Ord,Ix,Enum)

data Fact = Fact { fProp  :: !Pred
                 , fLevel :: !(IORef Word32)
                 , fOp    :: !OperRef
                 , fAdd   :: !Effects
                   -- ^ Effects that add this fact
                 , fDel   :: !Effects
                   -- ^ Effects that delete this fact
                 }

newtype OperRef = OperRef Int
                  deriving (Show,Eq,Ord,Ix,Enum)

data Oper = Oper { oEffects :: !Effects
                 }

newtype EffectRef = EffectRef Int
                    deriving (Show,Eq,Ord,Ix,Enum)

data Effect = Effect { ePre       :: !Facts
                     , eNumPre    :: !Word32
                     , eAdds      :: !Facts
                     , eDels      :: !Facts

                     , eLevel     :: !(IORef Word32)
                       -- ^ Membership level for this effect
                     , eActivePre :: !(IORef Word32)
                       -- ^ Active preconditions for this effect
                     }


-- | Reset all references in the plan graph to their initial state.
resetConnGraph :: ConnGraph -> IO ()
resetConnGraph ConnGraph { .. } =
  do amapM_ resetFact   cgFacts
     amapM_ resetOper   cgOpers
     amapM_ resetEffect cgEffects

resetFact :: Fact -> IO ()
resetFact Fact { .. } =
     writeIORef fLevel maxBound

resetOper :: Oper -> IO ()
resetOper Oper { .. } = return ()

resetEffect :: Effect -> IO ()
resetEffect Effect { .. } =
  do writeIORef eLevel maxBound
     writeIORef eActivePre 0


type Facts   = RefSet FactRef
type Goals   = RefSet FactRef
type State   = RefSet FactRef
type Effects = RefSet EffectRef

type Level   = Word32

-- | Loop until the goal state is activated in the connection graph.  As the
-- connection graph should only be built from domains that can activate all
-- facts, and delete effects are ignored, this operation will terminate.
buildFixpoint :: ConnGraph -> State -> Goals -> IO ()
buildFixpoint gr s0 g =
  do resetConnGraph gr
     loop 0 s0

  where
  loop level facts =
    do effs <- mconcat `fmap` mapM (activateFact gr level) (refs facts)
       done <- allGoalsReached gr g
       unless done $
         do facts' <- mconcat `fmap` mapM (activateEffect gr level) (refs effs)

            if isNull facts'
               then return ()
               else loop (level + 1) facts'


-- | All goals have been reached if they are all activated in the connection
-- graph.
allGoalsReached :: ConnGraph -> Goals -> IO Bool
allGoalsReached cg g = go goals
  where
  goals     = refs g

  -- require that all goals have a level that isn't infinity.
  go (r:rs) = do let Fact { .. } = cgFacts cg ! r
                 l <- readIORef fLevel
                 if l < maxBound
                    then go rs
                    else return False

  go []     =    return True


-- | Set a fact to true at this level of the relaxed graph.  Return any effects
-- that were enabled by adding this fact.
activateFact :: ConnGraph -> Level -> FactRef -> IO Effects
activateFact ConnGraph { .. } level ref =
  do let Fact { .. } = cgFacts ! ref
     writeIORef fLevel level

     mconcat `fmap` mapM addedPrecond (refs fAdd)

  where

  addedPrecond eff =
    do let Effect { .. } = cgEffects ! eff
       pcs <- readIORef eActivePre
       let pcs' = pcs + 1
       writeIORef eActivePre $! pcs'

       if pcs' == eNumPre
          then return (singleton eff)
          else return mempty

-- | Add an effect at level i, and return all of its add effects.
activateEffect :: ConnGraph -> Level -> EffectRef -> IO Facts
activateEffect ConnGraph { .. } level ref =
  do let Effect { .. } = cgEffects ! ref
     writeIORef eLevel level
     return eAdds


-- Utilities -------------------------------------------------------------------

amapM_ :: (Enum i, Ix i) => (e -> IO ()) -> Array i e -> IO ()
amapM_ f arr = go lo
  where
  (lo,hi) = bounds arr

  go i | i > hi    = return ()
       | otherwise = do f (arr ! i)
                        go (succ i)
