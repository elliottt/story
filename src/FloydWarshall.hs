module FloydWarshall where

import Control.Monad ( forM_, when, unless )
import Control.Monad.ST
import Data.Array.ST
import Data.Array.Unboxed
import Data.Graph


transitiveClosure :: Graph -> UArray (Int,Int) Bool
transitiveClosure graph = closure
  where
  closure = runST (freeze =<< floydWarshall graph)

floydWarshall :: Graph -> ST s (STUArray s (Int,Int) Bool)
floydWarshall graph =
  do dist <- newArray ((lo,lo),(hi,hi)) False

     forM_ ixs $ \ i ->
       -- initialize the graph
       do let vs = graph ! i
          forM_ vs $ \ j -> writeArray dist (i,j) True

     forM_ ixs $ \ k ->
       forM_ ixs $ \ i ->
         do ik <- readArray dist (i,k)
            when ik $ forM_ ixs $ \ j ->
                        do kj <- readArray dist (k,j)
                           when kj (writeArray dist (i,j) True)

     return dist

  where
  r@(lo,hi) = bounds graph
  ixs       = range r
