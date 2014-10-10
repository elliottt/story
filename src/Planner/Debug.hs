module Planner.Debug (
    dbg
  , zonkDbg
  ) where

import Plan
import Planner.Constraints ( bindings )
import Pretty

import Debug.Trace


debugEnabled :: Bool
debugEnabled  = False

{-# INLINE dbg #-}
dbg :: (Monad m, Show a) => String -> a -> m ()
dbg l a | debugEnabled = traceM (l ++ ": " ++ show a)
        | otherwise    = return ()

{-# INLINE zonkDbg #-}
zonkDbg :: (Monad m, PP a) => Plan -> String -> a -> m ()
zonkDbg p l a
  | debugEnabled =
    do sequence_ [ dbg (pretty v) d | (v, d) <- bindings (pBindings p) ]
       dbg l (pp a)

  | otherwise    =
       return ()

