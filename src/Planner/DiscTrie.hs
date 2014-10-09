{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Planner.DiscTrie (
    DiscTrie()
  , empty
  , insert
  , lookup
  , HasPath(..)

  , Facts
  , mkFacts

  , Domain
  , mkDomain
  , isRigid
  ) where

import           Prelude hiding ( lookup )

import           Planner.Types
                     ( Effect(..), Pred(..), negPred, Term(..), Schema(..)
                     , Action(..) )

import           Data.List ( foldl' )
import qualified Data.Map.Strict as Map


type DiscTrie a = Node a

empty :: DiscTrie a
empty  = Node Map.empty []

insert :: HasPath key => key -> a -> DiscTrie a -> DiscTrie a
insert key a t = insertPath (toPath key) a t


lookup :: HasPath key => key -> DiscTrie a -> [a]
lookup key = lookupPath (toPath key)


-- Utilities -------------------------------------------------------------------

type Facts = DiscTrie Pred

mkFacts :: [Pred] -> Facts
mkFacts  = foldl' addFact empty
  where
  addFact t p = insert p p t


type Domain = DiscTrie (Schema (Effect,Action))

mkDomain :: [Schema Action] -> Domain
mkDomain  = foldl' addEffect empty
  where
  addEffect    dom op@(Forall _ act) = foldl' (addAction op) dom (aEffect act)

  addAction op dom effect            = insert effect ((effect,) `fmap` op) dom

-- | Does this predicate show up in the effects of any action in the domain?
isRigid :: Domain -> Pred -> Bool
isRigid dom p = null (lookup p dom ++ lookup (negPred p) dom)


-- Tree Paths ------------------------------------------------------------------

type Path = [Sym]

data Sym = SPred Bool Int String
         | SCon String
         | SVar
           deriving (Show,Eq,Ord)

symExpect :: Sym -> Int
symExpect (SPred _ n _) = n
symExpect _             = 0

class HasPath a where
  toPath :: a -> Path

instance HasPath a => HasPath [a] where
  toPath = concatMap toPath

instance HasPath Sym where
  toPath = return

instance HasPath Term where
  toPath (TCon c) = [SCon c]
  toPath (TGen _) = [SVar]
  toPath (TVar _) = [SVar]

instance HasPath Pred where
  toPath (Pred n p ts) = SPred n (length ts) p : toPath ts

instance HasPath Effect where
  toPath (EPred p)      = toPath p
  toPath (EIntends a p) = SPred True 2 "intends" : toPath a ++ toPath p


-- Nodes -----------------------------------------------------------------------

data Node a = Node (Map.Map Sym (Node a)) [a]
              deriving (Show)


insertPath :: Path -> a -> Node a -> Node a

insertPath (p:ps) a (Node m as) = Node (Map.alter update p m) as
  where
  update (Just n) = Just (insertPath ps a n)
  update Nothing  = Just (insertPath ps a empty)

insertPath [] a (Node m as) = Node m (a:as)


lookupPath :: Path -> Node a -> [a]
lookupPath (p:ps) n           = lookupSym p ps n
lookupPath []     (Node _ as) = as

-- | Step one level during a lookup
lookupSym :: Sym -> Path -> Node a -> [a]
lookupSym SVar ps n          = concatMap (lookupPath ps) (dropPrefix 1 n)
lookupSym s    ps (Node m _) = find ps s ++ find (drop (symExpect s) ps) SVar
  where
  find ps' k = maybe [] (lookupPath ps') (Map.lookup k m)

dropPrefix :: Int -> Node a -> [Node a]
dropPrefix 0 node       = [node]
dropPrefix n (Node m _) = concatMap f (Map.toList m)
  where
  n'                        = n - 1
  f (SPred _ arity _, node) = dropPrefix (n' + arity) node
  f (_, node)               = dropPrefix  n'          node
