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

fromList :: Ref a => [a] -> RefSet a
fromList rs = RefSet (IS.fromList (map fromRef rs))

null :: RefSet a -> Bool
null (RefSet rs) = IS.null rs

empty :: RefSet a
empty  = RefSet IS.empty

singleton :: Ref a => a -> RefSet a
singleton a = RefSet (IS.singleton (fromRef a))

insert :: Ref a => a -> RefSet a -> RefSet a
insert a (RefSet rs) = RefSet (IS.insert (fromRef a) rs)
