{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ParallelListComp #-}

module FF.ConnGraph where

import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Control.Monad ( zipWithM )
import           Data.Array.IO
import           Data.IORef ( IORef, newIORef, readIORef, writeIORef )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as T


-- Connection Graph ------------------------------------------------------------

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


data Fact = Fact { fProp  :: !I.Fact
                 , fLevel :: !(IORef Level)

                 , fIsTrue:: !(IORef Level)
                 , fIsGoal:: !(IORef Bool)

                 , fPreCond :: !Effects
                   -- ^ Effects that require this fact
                 , fAdd   :: !Effects
                   -- ^ Effects that add this fact
                 , fDel   :: !Effects
                   -- ^ Effects that delete this fact
                 }

data Oper = Oper { oEffects :: !Effects
                   -- ^ Effects that correspond to instantiations of this
                   -- operator
                 , oName :: !T.Text
                 }

data Effect = Effect { ePre       :: !Facts
                     , eNumPre    :: !Int
                     , eAdds      :: !Facts
                     , eDels      :: !Facts
                     , eOp        :: !OperRef
                       -- ^ The operator that this effect came from

                     , eInPlan    :: !(IORef Bool)
                       -- ^ Whether or not this effect is a member of the
                       -- current relaxed plan

                     , eIsInH     :: !(IORef Bool)
                       -- ^ If this action is part of the helpful action set

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


-- Input Processing ------------------------------------------------------------

buildConnGraph :: I.Domain -> I.Problem -> IO (State,Goals,ConnGraph)
buildConnGraph dom prob =
  do facts   <- mapM mkFact allFacts
     cgFacts <- newListArray (FactRef 0, FactRef (length facts - 1)) facts

     opers   <- mapM mkOper (I.domOperators dom)
     cgOpers <- newListArray (OperRef 0, OperRef (length opers - 1)) opers

     effs      <- zipWithM (mkEffect cgOpers cgFacts) (map EffectRef [0 ..]) allEffs
     cgEffects <- newListArray (EffectRef 0, EffectRef (length effs - 1)) effs

     return (state,goal,ConnGraph { .. })

  where
  -- translated goal and initial state
  state = RS.fromList (map (factRefs Map.!) (I.probInit prob))
  goal  = RS.fromList (map (factRefs Map.!) (I.probGoal prob))

  -- all ground facts
  allFacts = Set.toList (I.probFacts prob `Set.union` I.domFacts dom)
  factRefs = Map.fromList (zip allFacts (map FactRef [0 ..]))

  -- all ground effects, extended with the preconditions from their operators
  allEffs = [ (oref, eff) | ix <- [ 0 .. ], let oref = OperRef ix
                          | op <- I.domOperators dom, eff <- I.expandEffects op
                          ]
  mkFact fProp =
    do fLevel  <- newIORef 0
       fIsTrue <- newIORef 0
       fIsGoal <- newIORef False
       return Fact { fPreCond = RS.empty
                   , fAdd     = RS.empty
                   , fDel     = RS.empty
                   , .. }

  mkOper op =
    do let oEffects = RS.empty
           oName    = I.opName op
       return Oper { .. }

  mkEffect opers facts ix (op,e) =
    do eLevel     <- newIORef 0
       eActivePre <- newIORef 0
       eInPlan    <- newIORef False
       eIsInH     <- newIORef False

       let refs fs = RS.fromList (map (factRefs Map.!) fs)
           eff     =  Effect { ePre    = refs (I.ePre e)
                             , eNumPre = length (I.ePre e)
                             , eAdds   = refs (I.eAdd e)
                             , eDels   = refs (I.eDel e)
                             , eOp     = op
                             , .. }

       Oper { .. } <- readArray opers op
       writeArray opers op Oper { oEffects = RS.insert ix oEffects, .. }

       -- add edges from the facts this effect's pre-conds/adds/deletes
       mapM_ pre (RS.toList (ePre  eff))
       mapM_ add (RS.toList (eAdds eff))
       mapM_ del (RS.toList (eDels eff))

       return eff

    where
    pre ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fPreCond = RS.insert ix fPreCond, .. }

    add ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fAdd = RS.insert ix fAdd, .. }

    del ref =
      do Fact { .. } <- readArray facts ref
         writeArray facts ref Fact { fDel = RS.insert ix fDel, .. }


-- Resetting -------------------------------------------------------------------

-- | Reset all references in the plan graph to their initial state.
resetConnGraph :: ConnGraph -> IO ()
resetConnGraph ConnGraph { .. } =
  do amapM_ resetFact   cgFacts
     amapM_ resetOper   cgOpers
     amapM_ resetEffect cgEffects

resetFact :: Fact -> IO ()
resetFact Fact { .. } =
  do writeIORef fLevel maxBound
     writeIORef fIsTrue 0
     writeIORef fIsGoal False


resetOper :: Oper -> IO ()
resetOper Oper { .. } = return ()

resetEffect :: Effect -> IO ()
resetEffect Effect { .. } =
  do writeIORef eLevel maxBound
     writeIORef eActivePre 0
     writeIORef eInPlan False
     writeIORef eIsInH False


-- Utilities -------------------------------------------------------------------

printFacts :: ConnGraph -> IO ()
printFacts ConnGraph { .. } = amapWithKeyM_ printFact cgFacts

printFact :: FactRef -> Fact -> IO ()
printFact ref Fact { .. } =
  do putStrLn ("Fact: (" ++ show ref ++ ") " ++ show fProp)

     lev    <- readIORef fLevel
     isTrue <- readIORef fIsTrue
     isGoal <- readIORef fIsGoal

     putStr $ unlines
       [ "  level:      " ++ show lev
       , "  is true:    " ++ show isTrue
       , "  is goal:    " ++ show isGoal
       , "  required by:" ++ show fPreCond
       , "  added by:   " ++ show fAdd
       , "  deleted by: " ++ show fDel
       ]

printEffects :: ConnGraph -> IO ()
printEffects ConnGraph { .. } = amapWithKeyM_ printEffect cgEffects

printEffect :: EffectRef -> Effect -> IO ()
printEffect ref Effect { .. } =
  do putStrLn ("Effect (" ++ show ref ++ ")")

     lev <- readIORef eLevel

     putStr $ unlines
       [ "  level: " ++ show lev
       ]

amapM_ :: (Enum i, Ix i) => (e -> IO ()) -> IOArray i e -> IO ()
amapM_ f arr =
  do (lo,hi) <- getBounds arr

     let go i | i > hi    =    return ()
              | otherwise = do f =<< readArray arr i
                               go (succ i)

     go lo

amapWithKeyM_ :: (Enum i, Ix i) => (i -> e -> IO ()) -> IOArray i e -> IO ()
amapWithKeyM_ f arr =
  do (lo,hi) <- getBounds arr

     let go i | i > hi    =    return ()
              | otherwise = do f i =<< readArray arr i
                               go (succ i)

     go lo
