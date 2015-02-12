{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

module FF.Compile.Trie where

import           Prelude hiding (lookup)

import           FF.Compile.AST

import           Control.Monad (MonadPlus(..),msum)
import           Data.List (nub)
import           Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as Map


class Functor t => Trie t where
  type Key t :: *
  empty  :: t a
  alter  :: (Maybe a -> Maybe a) -> Key t -> t a -> t a
  lookup :: Key t -> t a -> Maybe a
  match  :: MonadPlus m => Key t -> t a -> m a
  toList :: t a -> [(Key t,a)]

fromList :: Trie t => [(Key t, a)] -> t a
fromList  = foldl (\ t (k,a) -> insert k a t) empty
{-# INLINE fromList #-}

insert :: Trie t => Key t -> a -> t a -> t a
insert k a = alter (\ _ -> Just a) k
{-# INLINE insert #-}

insertWith :: Trie t => (a -> a -> a) -> Key t -> a -> t a -> t a
insertWith merge k a' = alter upd k
  where
  upd (Just a) = Just (merge a a')
  upd Nothing  = Just a'
{-# INLINE insertWith #-}


instance Ord k => Trie (Map.Map k) where
  type Key (Map.Map k) = k
  empty  = Map.empty
  alter  = Map.alter
  lookup = Map.lookup
  match k m = maybe mzero return (Map.lookup k m)
  toList = Map.toList


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


  lookup key List { .. } =
    case key of
      k:ks -> lookup ks =<< match k lCons
      []   -> lNil

  match key List { .. } =
    case key of
      k:ks -> match ks =<< match k lCons
      []   -> maybe mzero return lNil

  toList List { .. } =
    [ ([],   a) | Just a <- [lNil] ] ++
    [ (k:ks, a) | (k,m)  <- toList lCons
                , (ks,a) <- toList m ]


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
                           , ttLit    :: !(LitTrie a)
                           } deriving (Functor)

instance Trie TermTrie where
  type Key TermTrie = Term

  empty = TermTrie { ttAnd   = empty
                   , ttOr    = empty
                   , ttNot   = empty
                   , ttImply = empty
                   , ttForall= empty
                   , ttExists= empty
                   , ttLit   = empty
                   }

  alter f key TermTrie { .. } =
    case key of
      TAnd ts    -> TermTrie { ttAnd   = alter f ts ttAnd,  .. }
      TOr  ts    -> TermTrie { ttOr    = alter f ts ttOr,   .. }
      TNot t     -> TermTrie { ttNot   = alter f t  ttNot,  .. }
      TImply p q -> TermTrie { ttImply = alter (update f q) p ttImply, .. }
      TForall x p-> TermTrie { ttForall= alter (update f p) x ttForall, .. }
      TExists x p-> TermTrie { ttExists= alter (update f p) x ttExists, .. }
      TLit l     -> TermTrie { ttLit   = alter f l ttLit, .. }

  lookup key TermTrie { .. } =
    case key of
      TAnd ts    -> lookup ts ttAnd
      TOr  ts    -> lookup ts ttOr
      TNot t     -> lookup t  ttNot
      TImply p q -> lookup q =<< lookup p ttImply
      TForall x p-> lookup p =<< lookup x ttForall
      TExists x p-> lookup p =<< lookup x ttExists
      TLit l     -> lookup l  ttLit

  match key TermTrie { .. } =
    case key of
      TAnd ts    -> match ts ttAnd
      TOr  ts    -> match ts ttOr
      TNot t     -> match t  ttNot
      TImply p q -> match q =<< match p ttImply
      TForall x p-> match p =<< match x ttForall
      TExists x p-> match p =<< match x ttExists
      TLit l     -> match l  ttLit

  toList TermTrie { .. } =
    [ (TAnd ts,a)     | (ts,a) <- toList ttAnd ] ++
    [ (TOr  ts,a)     | (ts,a) <- toList ttOr  ] ++
    [ (TNot t,a)      | (t,a)  <- toList ttNot ] ++
    [ (TImply p q,a)  | (p,m)  <- toList ttImply
                      , (q,a)  <- toList m ] ++
    [ (TForall x p,a) | (x,m)  <- toList ttForall
                      , (p,a)  <- toList m ] ++
    [ (TExists x p,a) | (x,m)  <- toList ttExists
                      , (p,a)  <- toList m ] ++
    [ (TLit k,a)      | (k,a)  <- toList ttLit ]



data LitTrie a = LitTrie { lAtom :: AtomTrie a
                         , lNot  :: AtomTrie a
                         } deriving (Functor)

instance Trie LitTrie where
  type Key LitTrie = Literal

  empty = LitTrie empty empty

  alter f (LAtom a) LitTrie { .. } = LitTrie { lAtom = alter f a lAtom, .. }
  alter f (LNot  a) LitTrie { .. } = LitTrie { lAtom = alter f a lNot,  .. }

  lookup (LAtom a) LitTrie { .. } = lookup a lAtom
  lookup (LNot  a) LitTrie { .. } = lookup a lNot

  match (LAtom a) LitTrie { .. } = match a lAtom
  match (LNot  a) LitTrie { .. } = match a lNot

  toList LitTrie { .. } =
    [ (LAtom k,a) | (k,a) <- toList lAtom ] ++
    [ (LNot  k,a) | (k,a) <- toList lNot  ]



newtype AtomTrie a = AtomTrie (Map.Map Name (List ArgTrie a))
                     deriving (Functor)

instance Trie AtomTrie where
  type Key AtomTrie = Atom

  empty = AtomTrie empty

  alter f (Atom s as) (AtomTrie m) = AtomTrie (alter (update f as) s m)

  lookup (Atom s as) (AtomTrie m) = lookup as =<< lookup s m

  match (Atom s as) (AtomTrie m) = match as =<< match s m

  toList (AtomTrie m) = [ (Atom s as, a) | (s,b)  <- toList m
                                         , (as,a) <- toList b ]


data ArgTrie a = ArgTrie { atVar  :: !(Map.Map Name a)
                         , atName :: !(Map.Map Name a)
                         } deriving (Show,Functor)

instance Trie ArgTrie where
  type Key ArgTrie = Arg

  empty = ArgTrie { atVar = empty, atName = empty }

  alter f arg ArgTrie { .. } =
    case arg of
      AVar  n -> ArgTrie { atVar  = alter f n atVar,  .. }
      AName n -> ArgTrie { atName = alter f n atName, .. }

  lookup key ArgTrie { .. } =
    case key of
      AName n -> lookup n atName
      AVar n  -> lookup n atVar

  match key ArgTrie { .. } =
    case key of
      AName n -> match n atName `mplus` var
      AVar  _ -> allNames       `mplus` var
    where
    var = msum [ return x | x <- Map.elems atVar ]

    allNames = msum [ return x | x <- Map.elems atName ]

  toList ArgTrie { .. } =
    [ (AVar n,a)  | (n,a) <- toList atVar  ] ++
    [ (AName n,a) | (n,a) <- toList atName ]


-- | A map from type names to inhabitants.
type TypeMap = Map.Map Name [Name]

-- | Turn a list of operators into a mapping from type to inhabitants.
typeMap :: [Object] -> TypeMap
typeMap objs = nub `fmap` foldl addType empty objs
  where
  addType tm Typed { .. } = insertWith (++) tType [tValue] tm
