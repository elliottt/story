module Pretty (
    module Pretty
  , module Text.PrettyPrint.HughesPJ
  ) where

import qualified Data.Set as Set
import           Text.PrettyPrint.HughesPJ

commas :: [Doc] -> Doc
commas ds = fsep (punctuate (char ',') ds)

pretty :: PP a => a -> String
pretty a = show (pp a)

class PP a where
  pp :: a -> Doc

instance (PP a, PP b) => PP (a,b) where
  pp (a,b) = parens (commas [pp a, pp b])

instance PP a => PP [a] where
  pp as = brackets (commas (map pp as))

instance (Ord a, PP a) => PP (Set.Set a) where
  pp as = brackets (commas (map pp (Set.toList as)))
