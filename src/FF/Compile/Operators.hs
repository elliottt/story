{-# LANGUAGE RecordWildCards #-}

module FF.Compile.Operators (
  removeQuantifiers,
  removeDisjunction
  ) where

import           FF.Compile.AST
import qualified FF.Compile.Trie as Trie

import           Control.Monad (msum)
import qualified Data.Map as Map
import qualified Data.Text as T


-- Quantifiers -----------------------------------------------------------------

-- | Remove quantifiers used in the preconditions and effects of an operator, by
-- turning forall into conjuction, and exists into disjunction.
removeQuantifiers :: Trie.TypeMap -> Operator -> Operator
removeQuantifiers types Operator { .. } =
  Operator { opPrecond = rqTerm types opPrecond
           , opEffects = rqEff  types opEffects
           , ..
           }

type ArgEnv = Map.Map Name Arg

-- | Remove quantifiers from effects.
rqEff :: Trie.TypeMap -> Effect -> Effect
rqEff types = EAnd . go Map.empty
  where
  go env (EForall xs e) =
    do env' <- params xs env
       go env' e

  go env (EAnd es) =
       EAnd `fmap` mapM (go env) es

  go env (EWhen p qs) =
       return (EWhen (rqTerm' types env p) (map (substLit env) qs))

  go env (EPrim ls) =
       return (EPrim (map (substLit env) ls))

  params (Typed { .. } : ps) env =
    case Trie.lookup tType types of
      Just es -> do e <- es
                    params ps (Trie.insert tValue (AName e) env)
      Nothing -> []
  params [] env = return env

-- | Remove quantifiers from terms.
rqTerm :: Trie.TypeMap -> Term -> Term
rqTerm types = rqTerm' types Map.empty

rqTerm' :: Trie.TypeMap -> ArgEnv -> Term -> Term
rqTerm' types = go
  where
  go env (TAnd ts)      = TAnd (map (go env) ts)
  go env (TOr  ts)      = TOr  (map (go env) ts)
  go env (TNot t)       = TNot (go env t)
  go env (TImply p q)   = TImply (go env p) (go env q)
  go env (TForall xs p) = TAnd [ go env' p | env' <- params xs env ]
  go env (TExists xs p) = TOr  [ go env' p | env' <- params xs env ]
  go env (TAtom a)      = TAtom (substAtom env a)

  params (Typed { .. } : ps) env =
    case Trie.lookup tType types of
      Just es -> do e <- es
                    params ps (Trie.insert tValue (AName e) env)
      Nothing -> []

  params [] env = return env

substLit :: ArgEnv -> Literal -> Literal
substLit env (LNot  a) = LNot  (substAtom env a)
substLit env (LAtom a) = LAtom (substAtom env a)

substAtom :: ArgEnv -> Atom -> Atom
substAtom env (Atom s as) = Atom s (map subst as)
  where
  subst arg = case arg of
    AName _ -> arg
    AVar  n -> Map.findWithDefault arg n env


-- Disjunctive Preconditions ---------------------------------------------------

-- | Generate multiple
removeDisjunction :: Operator -> [Operator]
removeDisjunction Operator { .. } = zipWith mkOper [1 ..] (rdTerm opPrecond)
  where
  mkOper :: Int -> Term -> Operator
  mkOper ix pre =
    Operator { opName    = opName `T.append` T.pack (show ix)
             , opPrecond = pre
             , opDerived = True
             , .. }

-- | Remove disjunctions, by producing multiple terms.
rdTerm :: Term -> [Term]
rdTerm (TAnd ts)    = TAnd `fmap` mapM rdTerm ts
rdTerm (TOr ts)     = msum (map rdTerm ts)
rdTerm (TNot t)     = TNot `fmap` rdTerm t
rdTerm (TImply p q) = msum [ rdTerm (TNot p), rdTerm q ]
rdTerm a@TAtom{}    = return a
rdTerm TExists{}    = error "rdTerm: TExists"
rdTerm TForall{}    = error "rdTerm: TForall"
