{-# LANGUAGE RecordWildCards #-}
module FF.RefTrie where

import           Prelude hiding ( lookup )

import qualified FF.RefSet as RS

import qualified Data.IntMap.Strict as IM
import           Data.Maybe ( fromMaybe )


-- | A trie that uses a RefSet as its key.
data RefTrie r a = RefTrie { rtEmpty :: !(Maybe a)
                           , rtNode  :: !(IM.IntMap (RefTrie r a))
                           } deriving (Show)

empty :: RefTrie r a
empty  = RefTrie { rtEmpty = Nothing
                 , rtNode  = IM.empty
                 }

singleton :: RS.Ref r => RS.RefSet r -> a -> RefTrie r a
singleton rs a = insert rs a empty

insert :: RS.Ref r => RS.RefSet r -> a -> RefTrie r a -> RefTrie r a
insert key a rt = go key rt
  where
  go rs RefTrie { .. } =
    case RS.minView rs of

      Just (r,rs') ->
        let upd (Just m) = Just (go rs' m)
            upd Nothing  = Just (go rs' empty)
         in RefTrie { rtNode  = IM.alter upd (RS.fromRef r) rtNode, ..  }

      Nothing -> RefTrie { rtEmpty = Just a, .. }

lookup :: RS.Ref r => RS.RefSet r -> RefTrie r a -> Maybe a
lookup rs RefTrie { .. }
  | RS.null rs =    rtEmpty
  | otherwise  = do (key,rs') <- RS.minView rs
                    sub       <- IM.lookup (RS.fromRef key) rtNode
                    lookup rs' sub

findWithDefault :: RS.Ref r => a -> RS.RefSet r -> RefTrie r a -> a
findWithDefault def rs rt = fromMaybe def (lookup rs rt)
