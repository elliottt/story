{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

module FF.Compile.Trie where

import           Prelude hiding (lookup)

import           FF.Compile.AST

import           Control.Monad (MonadPlus(..))
import           Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map


class Trie t where
  type Key t :: *
  empty  :: t a
  alter  :: (Maybe a -> Maybe a) -> Key t -> t a -> t a
  match  :: MonadPlus m => Key t -> t a -> m a

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

  match k m = maybe mzero return (Map.lookup k m)


data List t a = List { lNil  :: !(Maybe a)
                     , lCons :: !(t (List t a))
                     } deriving (Functor)

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
      []   -> case lNil of
                Just a  -> return a
                Nothing -> mzero


-- | Turn a single alter function into one that can be used on tries of tries.
update :: Trie t
       => (Maybe a -> Maybe a) -> Key t -> (Maybe (t a) -> Maybe (t a))
update f k m = Just $! alter f k $! fromMaybe empty m


data TermTrie a = TermTrie { ttAnd    :: !(List TermTrie a)
                           , ttOr     :: !(List TermTrie a)
                           , ttNot    :: !(TermTrie a)
                           , ttImply  :: !(TermTrie (TermTrie a))
                           , ttForall :: !(List (Map.Map Param) (TermTrie a))
                           , ttExists :: !(List (Map.Map Param) (TermTrie a))
                           , ttAtom   :: !(AtomTrie a)
                           } deriving (Functor)

instance Trie TermTrie where
  type Key TermTrie = Term

  empty = TermTrie { ttAnd   = empty
                   , ttOr    = empty
                   , ttNot   = empty
                   , ttImply = empty
                   , ttForall= empty
                   , ttExists= empty
                   , ttAtom  = empty
                   }

  alter f key TermTrie { .. } =
    case key of
      TAnd ts    -> TermTrie { ttAnd   = alter f ts ttAnd,  .. }
      TOr  ts    -> TermTrie { ttOr    = alter f ts ttOr,   .. }
      TNot t     -> TermTrie { ttNot   = alter f t  ttNot,  .. }
      TImply p q -> TermTrie { ttImply = alter (update f q) p ttImply, .. }
      TForall x p-> TermTrie { ttForall= alter (update f p) x ttForall, .. }
      TExists x p-> TermTrie { ttExists= alter (update f p) x ttExists, .. }
      TAtom a    -> TermTrie { ttAtom  = alter f a ttAtom, .. }

  match key TermTrie { .. } =
    case key of
      TAnd ts    -> match ts ttAnd
      TOr  ts    -> match ts ttOr
      TNot t     -> match t  ttNot
      TImply p q -> match q =<< match p ttImply
      TForall x p-> match p =<< match x ttForall
      TExists x p-> match p =<< match x ttExists
      TAtom a    -> match a  ttAtom


newtype AtomTrie a = AtomTrie (Map.Map Name (List ArgTrie a))
                     deriving (Functor)

instance Trie AtomTrie where
  type Key AtomTrie = Atom

  empty = AtomTrie empty

  alter f (Atom s as) (AtomTrie m) = AtomTrie (alter (update f as) s m)

  match (Atom s as) (AtomTrie m) = match as =<< match s m


data ArgTrie a = ArgTrie { atVar  :: !(Maybe a)
                         , atName :: !(Map.Map Name a)
                         } deriving (Show,Functor)

instance Trie ArgTrie where
  type Key ArgTrie = Arg

  empty = ArgTrie { atVar = Nothing, atName = empty }

  alter f arg ArgTrie { .. } =
    case arg of
      AVar  _ -> ArgTrie { atVar = f atVar, .. }
      AName n -> ArgTrie { atName = alter f n atName, .. }

  match key ArgTrie { .. } =
    case key of
      AName n -> match n atName `mplus` var
      AVar  _ -> var
    where
    var = case atVar of
            Just a  -> return a
            Nothing -> mzero

