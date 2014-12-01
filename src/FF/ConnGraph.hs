{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}

module FF.ConnGraph where

import qualified FF.Input as I
import qualified FF.RefSet as RS

import           Control.Monad ( zipWithM )
import           Data.Array.IO
import           Data.IORef ( IORef, newIORef, readIORef )
import qualified Data.Set as Set
import qualified Data.Map as Map


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


-- Input Processing ------------------------------------------------------------

buildConnGraph :: I.Problem -> I.Domain -> IO ConnGraph
buildConnGraph prob dom =
  do cgOpers   <- newListArray (OperRef 0, OperRef (length opers - 1)) opers


     facts   <- mapM mkFact allFacts
     cgFacts <- newListArray (FactRef 0, FactRef (length facts - 1)) facts

     effs      <- zipWithM (mkEffect cgFacts) (map EffectRef [0 ..]) allEffs
     cgEffects <- newListArray (EffectRef 0, EffectRef (length effs - 1)) effs

     return ConnGraph { .. }

  where
  -- all ground facts
  allFacts = Set.toList (I.probFacts prob `Set.union` I.domFacts dom)
  factRefs = Map.fromList (zip allFacts (map FactRef [0 ..]))

  -- all ground effects, extended with the preconditions from their operators
  expanded = map I.expandEffects (I.domOperators dom)
  allEffs  = concat expanded
  effRefs  = Map.fromList (zip allEffs (map EffectRef [0 ..]))

  -- operators, with references to their effects
  opers     = map mkOper expanded
  mkOper es = Oper { oEffects = RS.fromList (map (effRefs Map.!) es) }

  mkFact fProp =
    do fLevel  <- newIORef 0
       fIsTrue <- newIORef 0
       fIsGoal <- newIORef False
       return Fact { fPreCond = RS.empty
                   , fAdd     = RS.empty
                   , fDel     = RS.empty
                   , .. }

  mkEffect facts ix e =
    do eLevel     <- newIORef 0
       eActivePre <- newIORef 0


       let refs fs = RS.fromList (map (factRefs Map.!) fs)
           eff     =  Effect { ePre    = refs (I.ePre e)
                             , eNumPre = length (I.ePre e)
                             , eAdds   = refs (I.eAdd e)
                             , eDels   = refs (I.eDel e)
                             , .. }

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


-- Utilities -------------------------------------------------------------------

printFacts :: ConnGraph -> IO ()
printFacts ConnGraph { .. } = amapM_ printFact cgFacts

printFact :: Fact -> IO ()
printFact Fact { .. } =
  do putStrLn ("Fact: " ++ show fProp)

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

amapM_ :: (Enum i, Ix i) => (e -> IO ()) -> IOArray i e -> IO ()
amapM_ f arr =
  do (lo,hi) <- getBounds arr

     let go i | i > hi    =    return ()
              | otherwise = do f =<< readArray arr i
                               go (succ i)

     go lo
