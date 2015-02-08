{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

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
removeDisjunction Operator { .. } = zipWith mkOper [1 ..] rdOper
  where

  rdOper = do pre <- rdTerm   (nnfTerm   opPrecond)
              eff <- rdEffect (nnfEffect opEffects)
              return (pre,eff)

  mkOper ix (pre,eff) =
    Operator { opName    = T.concat [ opName, "-", T.pack (show (ix :: Int)) ]
             , opPrecond = pre
             , opEffects = eff
             , opDerived = True
             , .. }

-- | Remove disjunctions, by producing multiple terms.
rdTerm :: Term -> [Term]
rdTerm (TAnd ts)       = TAnd `fmap` mapM rdTerm ts
rdTerm (TOr ts)        = msum (map rdTerm ts)
rdTerm (TNot t)        = TNot `fmap` rdTerm t
rdTerm a@TAtom{}       = return a
rdTerm TImply{}        = error "rdTerm: TImply"
rdTerm TExists{}       = error "rdTerm: TExists"
rdTerm TForall{}       = error "rdTerm: TForall"

rdEffect :: Effect -> [Effect]
rdEffect (EWhen t q) = do p <- rdTerm t
                          return (EWhen p q)
rdEffect (EAnd es)   =    EAnd `fmap` map rdEffect es
rdEffect e@EPrim{}   =    return e
rdEffect EForall{}   = error "nnfEffect: EForall"

-- | Put a term in negation normal form.
nnfTerm :: Term -> Term

nnfTerm (TNot (TNot t))     = nnfTerm t
nnfTerm (TNot (TAnd ts))    = TOr  (map (nnfTerm . TNot) ts)
nnfTerm (TNot (TOr  ts))    = TAnd (map (nnfTerm . TNot) ts)
nnfTerm (TNot (TImply p q)) = TAnd [nnfTerm p, nnfTerm (TNot q)]
nnfTerm t@(TNot TAtom{})    = t

nnfTerm (TAnd ts)           = TAnd (map nnfTerm ts)
nnfTerm (TOr  ts)           = TOr  (map nnfTerm ts)

-- instead of just translating to (-p \/ q), produce (-p \/ (p /\ q)).  This is
-- redundant in the logical sense, but when disjunction gets removed, it
-- produces something that's a little more true to the intent: two rules, one
-- for -p and one for p /\ q.
nnfTerm (TImply p q)        = TOr  [ nnfTerm (TNot p)
                                   , TAnd [ nnfTerm p, nnfTerm q ] ]

nnfTerm t@TAtom{}           = t

nnfTerm (TNot TForall{})    = error "nnfTerm: TForall"
nnfTerm (TNot TExists{})    = error "nnfTerm: TForall"
nnfTerm TForall{}           = error "nnfTerm: TForall"
nnfTerm TExists{}           = error "nnfTerm: TExists"

nnfEffect :: Effect -> Effect
nnfEffect (EWhen p q) = EWhen (nnfTerm p) q
nnfEffect (EAnd es)   = EAnd (map nnfEffect es)
nnfEffect e@EPrim{}   = e
nnfEffect EForall{}   = error "nnfEffect: EForall"
