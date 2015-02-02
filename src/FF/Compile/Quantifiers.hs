{-# LANGUAGE RecordWildCards #-}

module FF.Compile.Quantifiers where

import           FF.Compile.AST
import qualified FF.Compile.Trie as Trie

import           Data.List (nub)
import qualified Data.Map as Map


-- | Remove quantifiers from the domain, by turning forall into conjuction, and
-- exists into disjunction.
removeQuantifiers :: [Object] -> Domain -> Domain
removeQuantifiers objs Domain { .. } =
  Domain { domOperators = map (rqOp types) domOperators
         , .. }
  where

  types = typeMap objs

-- | A map from type names to inhabitants.
type TypeMap = Map.Map Name [Name]

-- | Turn a list of operators into a mapping from type to inhabitants.
typeMap :: [Object] -> TypeMap
typeMap objs = nub `fmap` foldl addType Trie.empty objs
  where
  addType tm Typed { .. } = Trie.insertWith (++) tType [tValue] tm


-- | Remove quantifiers from 
rqOp :: TypeMap -> Operator -> Operator
rqOp types Operator { .. } =
  Operator { opPrecond = map (rqTerm types) opPrecond
           , opEffects = map (rqEff  types) opEffects
           , ..
           }

rqEff :: TypeMap -> Effect -> Effect
rqEff  = rqTerm

rqTerm :: TypeMap -> Term -> Term
rqTerm types = go Map.empty
  where
  go env (TAnd ts)           = TAnd (map (go env) ts)
  go env (TOr  ts)           = TOr  (map (go env) ts)
  go env (TNot t)            = TNot (go env t)
  go env (TImply p q)        = TImply (go env p) (go env q)
  go env (TForall xs p)      = TAnd [ go env' p | env' <- params xs env ]
  go env (TExists xs p)      = TOr  [ go env' p | env' <- params xs env ]
  go env (TAtom (Atom s as)) = TAtom (Atom s [ subst env a | a <- as ])

  params (Typed { .. } : ps) env =
    case Trie.lookup tType types of
      Just es -> do e <- es
                    params ps (Trie.insert tValue (AName e) env)
      Nothing -> []

  params [] env = return env

  subst env arg = case arg of
    AName _ -> arg
    AVar  n -> Map.findWithDefault arg n env
