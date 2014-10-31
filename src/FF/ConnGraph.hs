{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FF.ConnGraph where

import qualified FF.RefSet as RS

import           Data.Array.IO
import           Data.IORef ( IORef )


-- Connection Graph ------------------------------------------------------------

-- | Ground, positive predicates.
data Pred = Pred String [String]
            deriving (Show,Eq,Ord)

type Facts   = RS.RefSet FactRef
type Goals   = RS.RefSet FactRef
type State   = RS.RefSet FactRef
type Effects = RS.RefSet EffectRef

type Level   = Int

data ConnGraph = ConnGraph { cgFacts   :: !(IOArray FactRef Fact)
                           , cgOpers   :: !(IOArray OperRef Oper)
                           , cgEffects :: !(IOArray EffectRef Effect)
                           }

newtype FactRef = FactRef Int
                  deriving (Show,Eq,Ord,Ix,Enum)

newtype OperRef = OperRef Int
                  deriving (Show,Eq,Ord,Ix,Enum)

newtype EffectRef = EffectRef Int
                    deriving (Show,Eq,Ord,Ix,Enum)


data Fact = Fact { fProp  :: !Pred
                 , fLevel :: !(IORef Level)

                 , fIsTrue:: !(IORef Level)
                 , fIsGoal:: !(IORef Bool)

                 , fOp    :: !OperRef
                 , fAdd   :: !Effects
                   -- ^ Effects that add this fact
                 , fDel   :: !Effects
                   -- ^ Effects that delete this fact
                 }

data Oper = Oper { oEffects :: !Effects
                 }

data Effect = Effect { ePre       :: !Facts
                     , eNumPre    :: !Int
                     , eAdds      :: !Facts
                     , eDels      :: !Facts

                     , eLevel     :: !(IORef Level)
                       -- ^ Membership level for this effect
                     , eActivePre :: !(IORef Level)
                       -- ^ Active preconditions for this effect
                     }



instance RS.Ref FactRef where
  toRef               = FactRef
  fromRef (FactRef r) = r

instance RS.Ref EffectRef where
  toRef                 = EffectRef
  fromRef (EffectRef r) = r
