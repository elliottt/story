{-# LANGUAGE RecordWildCards #-}
module FF.Compile (
    compile
  , module FF.Compile.AST
  ) where

import           FF.Compile.AST
import           FF.Compile.Problem
import           FF.Compile.Operators
import qualified FF.Compile.Trie as Trie
import qualified FF.Input as I

import           Data.Foldable (foldMap)
import qualified Data.Text as T


compile :: Problem -> Domain -> (I.Problem,I.Domain)
compile prob dom = ( transProblem prob'
                   , transDomain dom { domOperators = ops' } )
  where
  types = Trie.typeMap (probObjects prob)

  (prob',initAndGoal) = genProblemOperators prob

  ops' = removeNegation $
    do op <- map (removeQuantifiers types) (initAndGoal ++ domOperators dom)
       removeDisjunction op


transProblem :: Problem -> I.Problem
transProblem Problem { .. } =
  I.Problem { I.probInit = [ transAtom a | LAtom a <- probInit ]
            , I.probGoal = transPre probGoal
            }

transDomain :: Domain -> I.Domain
transDomain Domain { .. } =
  I.Domain { I.domOperators = map transOperator domOperators }

transOperator :: Operator -> I.Operator
transOperator Operator { .. } =
  I.Operator { I.opName    = opName
             , I.opPre     = transPre opPrecond
             , I.opEffects = transEff opEffects
             }

transPre :: Term -> [I.Fact]
transPre (TAnd ts)        = concatMap transPre ts
transPre (TLit (LAtom a)) = [transAtom a]
transPre _                = error "transTerm"

transEff :: Effect -> [I.Effect]
transEff eff = simple ++ conditional
  where
  (lits,conds) = splitEffs eff

  simple | null lits = []
         | otherwise = [ foldl addEffect emptyEffect lits ]

  conditional =
    [ foldl addEffect eff q | (p,q) <- conds
                            , let eff = emptyEffect { I.ePre = transPre p } ]

  emptyEffect = I.Effect { I.ePre = [], I.eAdd = [], I.eDel = [] }

  addEffect eff (LAtom a) = eff { I.eAdd = transAtom a : I.eAdd eff }
  addEffect eff (LNot  a) = eff { I.eDel = transAtom a : I.eDel eff }

-- | Partition an effect into its simple, and conditional effects.
splitEffs :: Effect -> ([Literal],[(Term,[Literal])])
splitEffs eff = go [] [] (elimEAnd eff)
  where
  go ls cs (EWhen p q : rest) = go    ls ((p,q):cs) rest
  go ls cs (ELit l    : rest) = go (l:ls)       cs  rest
  go ls cs []                 = (ls,cs)
  go _  _  _                  = error "splitEffs"

transAtom :: Atom -> I.Fact
transAtom (Atom a as) = I.Fact a (map transArg as)

transArg :: Arg -> T.Text
transArg (AName n) = n
transArg _         = error "transArg"
