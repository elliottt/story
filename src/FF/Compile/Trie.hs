{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}

module FF.Compile.Trie where

import           Prelude hiding (lookup)

import           FF.Compile.AST

import           Data.Maybe (maybeToList, fromMaybe)
import qualified Data.Map.Strict as Map


class Trie t where
  type Key t :: *
  empty  :: t a
  alter  :: (Maybe a -> Maybe a) -> Key t -> t a -> t a
  match  :: Key t -> t a -> [a]

fromList :: Trie t => [(Key t, a)] -> t a
fromList  = foldl (\ t (k,a) -> insert k a t) empty
{-# INLINE fromList #-}

insert :: Trie t => Key t -> a -> t a -> t a
insert k a = alter (\ _ -> Just a) k
{-# INLINE insert #-}


instance Ord k => Trie (Map.Map k) where
  type Key (Map.Map k) = k
  empty  = Map.empty
  alter  = Map.alter

  match k m = maybeToList (Map.lookup k m)


data List t a = List { lNil  :: !(Maybe a)
                     , lCons :: !(t (List t a))
                     }

instance Trie t => Trie (List t) where
  type Key (List t) = [Key t]

  empty = List { lNil = Nothing, lCons = empty }

  alter f key List { .. } =
    case key of
      k:ks -> List { lCons = alter (update f ks) k lCons, .. }
      []   -> List { lNil  = f lNil, .. }

  match key List { .. } =
    case key of
      k:ks -> match ks =<< match k lCons
      []   -> maybeToList lNil


-- | Turn a single alter function into one that can be used on tries of tries.
update :: Trie t
       => (Maybe a -> Maybe a) -> Key t -> (Maybe (t a) -> Maybe (t a))
update f k m = Just $! alter f k $! fromMaybe empty m



newtype AtomTrie a = AtomTrie (Map.Map Name (List ArgTrie a))

instance Trie AtomTrie where
  type Key AtomTrie = Atom

  empty = AtomTrie empty

  alter f (Atom s as) (AtomTrie m) = AtomTrie (alter (update f as) s m)

  match (Atom s as) (AtomTrie m) = match as =<< match s m


data ArgTrie a = ArgTrie { atVar  :: !(Maybe a)
                         , atName :: !(Map.Map Name a)
                         } deriving (Show)

instance Trie ArgTrie where
  type Key ArgTrie = Arg

  empty = ArgTrie { atVar = Nothing, atName = empty }

  alter f arg ArgTrie { .. } =
    case arg of
      AVar  _ -> ArgTrie { atVar = f atVar, .. }
      AName n -> ArgTrie { atName = alter f n atName, .. }

  match key ArgTrie { .. } =
    case key of
      AName n -> match n atName ++ maybeToList atVar
      AVar  _ -> Map.elems atName ++ maybeToList atVar
