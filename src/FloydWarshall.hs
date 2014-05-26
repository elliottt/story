module FloydWarshall where

import Control.Monad ( forM_, when )
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
         forM_ ixs $ \ j ->
           do ij <- readArray dist (i,j)
              ik <- readArray dist (i,k)
              kj <- readArray dist (k,j)
              when (ik && kj || ij) (writeArray dist (i,j) True)
     return dist

  where
  r@(lo,hi) = bounds graph
  ixs       = range r
