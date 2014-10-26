{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module FF.RefSet where

import qualified Data.IntSet as IS
import           Data.Monoid ( Monoid )


-- Reference Sets --------------------------------------------------------------

newtype RefSet a = RefSet IS.IntSet
                   deriving (Show,Eq,Monoid)

class Ref a where
  toRef   :: Int -> a
  fromRef :: a -> Int

toList :: Ref a => RefSet a -> [a]
toList (RefSet is) = [ toRef r | r <- IS.toList is ]

null :: RefSet a -> Bool
null (RefSet rs) = IS.null rs

singleton :: Ref a => a -> RefSet a
singleton a = RefSet (IS.singleton (fromRef a))

