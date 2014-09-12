module Pretty (
    module Pretty
  , module Text.PrettyPrint.HughesPJ
  ) where

import           Data.Graph ( SCC(..) )
import qualified Data.Set as Set
import           Text.PrettyPrint.HughesPJ

commas :: [Doc] -> Doc
commas ds = fsep (punctuate (char ',') ds)

angles :: Doc -> Doc
angles p = char '<' <> p <> char '>'

pretty :: PP a => a -> String
pretty a = show (pp a)

class PP a where
  pp :: a -> Doc

instance PP Doc where
  {-# INLINE pp #-}
  pp x = x

instance PP a => PP (SCC a) where
  pp (AcyclicSCC a) = text "Acyclic" <+> pp a
  pp (CyclicSCC as) = text "Cyclic" <+> pp as

instance (PP a, PP b) => PP (Either a b) where
  pp (Left  a) = text "Left"  <+> pp a
  pp (Right b) = text "Right" <+> pp b

instance (PP a, PP b) => PP (a,b) where
  pp (a,b) = parens (commas [pp a, pp b])

instance (PP a, PP b, PP c) => PP (a,b,c) where
  pp (a,b,c) = parens (commas [pp a, pp b, pp c])

instance PP a => PP [a] where
  pp as = brackets (commas (map pp as))

instance (Ord a, PP a) => PP (Set.Set a) where
  pp as = brackets (commas (map pp (Set.toList as)))
