{-# LANGUAGE RecordWildCards #-}

module DiscTrie where

import           Types

import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe )


type DiscTrie a = Map.Map Sym (Node a)

empty :: DiscTrie a
empty  = Map.empty

insert :: Pred -> a -> DiscTrie a -> DiscTrie a
insert Pred { .. } a t = Map.alter update sym t
  where
  sym = SPred pNeg (length pArgs) pSym

  update (Just node) = Just (insertTerms pArgs a node)
  update Nothing     = Just (insertTerms pArgs a emptyNode)

lookup :: Pred -> DiscTrie a -> [a]
lookup Pred { .. } t =
  case Map.lookup sym t of
    Just node -> lookupTerms pArgs node
    Nothing   -> []
  where
  sym = SPred pNeg (length pArgs) pSym


-- Nodes -----------------------------------------------------------------------

data Sym = SPred Bool Int String
         | SCon String
           deriving (Show,Eq,Ord)

-- | Produces a Nothing in the case that the term is a variable.
isSym :: Term -> Maybe (Sym,[Term])
isSym (TCon c)            = Just (SCon c, [])
isSym (TPred Pred { .. }) = Just (SPred pNeg (length pArgs) pSym, pArgs)
isSym TGen{}              = Nothing
isSym TVar{}              = Nothing

data Node a = Node (Maybe (Node a)) (Map.Map Sym (Node a)) [a]
              deriving (Show)

emptyNode :: Node a
emptyNode  = Node Nothing Map.empty []

insertTerms :: [Term] -> a -> Node a -> Node a

insertTerms (t:ts) a (Node mbStar m as) =
  case isSym t of
    Just (sym,args) -> Node mbStar (Map.alter (update args) sym m) as
    Nothing         -> Node (Just (insertTerms ts a star)) m as
  where
  star                    = fromMaybe emptyNode mbStar
  update args (Just node) = Just (insertTerms (args ++ ts) a node)
  update args Nothing     = Just (insertTerms (args ++ ts) a emptyNode)

insertTerms [] a (Node mbStar m as) = Node mbStar m (a:as)


lookupTerms :: [Term] -> Node a -> [a]

lookupTerms (t:ts) (Node mbStar m _) = specific ++ lookupStar
  where
  lookupStar = maybe [] (lookupTerms ts)           mbStar

  specific =
    case isSym t of
      Just (sym,args) -> maybe [] (lookupTerms (args ++ ts)) (Map.lookup sym m)
      Nothing         -> concatMap (lookupTerms ts) (Map.elems m)

lookupTerms [] (Node _ _ as) = as
