module FF.Compile where

import           FF.Compile.AST
import           FF.Compile.Problem
import           FF.Compile.Operators
import qualified FF.Compile.Trie as Trie


compile :: Problem -> Domain -> (Problem,Domain)
compile prob dom = (prob',dom { domOperators = ops' })
  where
  types = Trie.typeMap (probObjects prob)

  (prob',initAndGoal) = genProblemOperators prob

  ops' =
    do op <- map (removeQuantifiers types) (initAndGoal ++ domOperators dom)
       removeDisjunction op
