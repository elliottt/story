module Unify where

import Types

import qualified Data.Map as Map
import qualified Data.Set as Set
import           MonadLib


-- | Variable environment.
type Env = Map.Map Int Term

data Error = UnificationFailed Term Term
           | MatchingFailed    Term Term
           | OccursCheckFailed Term Term
             deriving (Show)

-- | Unify two terms.
mgu :: Env -> Term -> Term -> Either Error Env
mgu env0 t1 t2 = runId (runExceptionT (go env0 t1 t2))
  where
  go env (TCon a) (TCon b)
    | a == b = return env

  go env (TApp f x) (TApp g y) =
    do env' <- go env f g
       go env' x y

  go env (TVar i) (TVar j)
    | i == j = return env

  go env (TVar v) r
    | Just l' <- Map.lookup i env = go env l' r
    | otherwise                   = return (Map.insert i r env)
    where
    i = varIndex v

  go env l r@TVar{} =
    go env r l

  go _ l r =
    raise (UnificationFailed l r)

-- | Match two terms with each other.
match :: Env -> Term -> Term -> Either Error Env
match env0 t1 t2 = runId (runExceptionT (go env0 t1 t2))
  where
  go env (TCon a) (TCon b)
    | a == b = return env

  go env (TApp f x) (TApp g y) =
    do env' <- go env f g
       go env' x y

  go env (TVar i) (TVar j)
    | i == j = return env

  go env (TVar v) r
    | Just l' <- Map.lookup i env = go env l' r
    | otherwise                   = return (Map.insert i r env)
    where
    i = varIndex v

  go _ l r =
    raise (MatchingFailed l r)

-- | Remove unification variables from a term.
zonk :: Env -> Term -> Either Error Term
zonk env = runId . runExceptionT . go Set.empty
  where

  go seen (TApp l r) =
    do l' <- go seen l
       r' <- go seen r
       return (TApp l' r')

  go seen tm@(TVar v) =
    case Map.lookup i env of
      Just tm' | Set.member i seen -> raise (OccursCheckFailed tm tm')
               | otherwise         -> go (Set.insert i seen) tm'
      Nothing                      -> return tm
    where
    i = varIndex v

  go _ tm =
    return tm
