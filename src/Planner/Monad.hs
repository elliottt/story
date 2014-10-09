{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Planner.Monad (
    PlanM()
  , runPlanM
  , freshVar
  , findAction
  , getFacts
  , choose

  , panic
  ) where

import qualified Planner.DiscTrie as D
import           Planner.Types ( Effect, Schema, Action )

import           Control.Applicative ( Applicative(..), Alternative(..) )
import qualified Control.Exception as X
import           Control.Monad ( MonadPlus(..) )
import qualified Data.Foldable as F
import           Data.Typeable ( Typeable )


-- External Interface ----------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: forall r. RW -> r -> (RW -> a -> r) -> r }

instance Functor PlanM where
  {-# INLINE fmap #-}
  fmap f m = PlanM $ \ s  e k ->
     unPlanM m s e $ \ s' a   -> k s' (f a)

instance Applicative PlanM where
  {-# INLINE pure #-}
  pure a = PlanM (\ s _ k -> k s a )

  {-# INLINE (<*>) #-}
  f <*> x = PlanM $ \ s0 e k ->
   unPlanM f s0 e $ \ s1 g   ->
   unPlanM x s1 e $ \ s2 y   -> k s2 (g y)

instance Alternative PlanM where
  {-# INLINE empty #-}
  empty = PlanM (\ _ e _ -> e)

  {-# INLINE (<|>) #-}
  a <|> b = PlanM (\ s e k -> unPlanM a s (unPlanM b s e k) k)

instance Monad PlanM where
  {-# INLINE return #-}
  return = pure

  {-# INLINE (>>=) #-}
  m >>= f = PlanM $ \ s  e k ->
    unPlanM m s e $ \ s' a   -> unPlanM (f a) s' e k

instance MonadPlus PlanM where
  {-# INLINE mzero #-}
  mzero = empty

  {-# INLINE mplus #-}
  mplus = (<|>)


runPlanM :: D.Facts -> D.Domain -> PlanM a -> Maybe a
runPlanM rwFacts rwDomain (PlanM f) = f rw Nothing final
  where
  rw        = RW { rwNextVar = 0, .. }
  final _ a = Just a

-- | Generate a fresh variable index.
freshVar :: PlanM Int
freshVar  =
  do rw <- getRW
     setRW rw { rwNextVar = rwNextVar rw + 1 }
     return (rwNextVar rw)

-- | Choose an element of a list.  Left-biased, backtracking on failure.
choose :: [a] -> PlanM a
choose [a] = pure a
choose as  = F.asum (map pure as)

-- | Find Actions that have effects that may satisfy the given predicate.
findAction :: Effect -> PlanM [Schema (Effect,Action)]
findAction p =
  do RW { .. } <- getRW
     return (D.lookup p rwDomain)

getFacts :: PlanM D.Facts
getFacts  =
  do RW { .. } <- getRW
     return rwFacts


data Panic = Panic String
             deriving (Typeable,Show)

instance X.Exception Panic

panic :: String -> PlanM a
panic msg = X.throw (Panic msg)


-- Internal State --------------------------------------------------------------

data RW = RW { rwNextVar :: !Int
             , rwFacts   :: D.Facts
             , rwDomain  :: D.Domain
             } deriving (Show)

{-# INLINE getRW #-}
getRW :: PlanM RW
getRW  = PlanM (\s _ k -> k s s)

{-# INLINE setRW #-}
setRW :: RW -> PlanM ()
setRW s = PlanM (\_ _ k -> k s ())
