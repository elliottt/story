{-# LANGUAGE GeneralizedNewtypeDeriving #-}

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

  go env (TBound i) (TBound j)
    | i == j = return env

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

  go env (TBound i) (TBound j)
    | i == j = return env

  go env (TVar i) (TVar j)
    | i == j = return env

  go env (TVar v) r
    | Just l' <- Map.lookup i env = go env l' r
    | otherwise                   = return (Map.insert i r env)
    where
    i = varIndex v

  go _ l r =
    raise (MatchingFailed l r)

newtype Zonk a = Zonk { unZonk :: ReaderT Env (StateT (Set.Set Int)
                                              (ExceptionT Error Id)) a
                      } deriving (Functor,Monad)

-- | Remove unification variables from a term.
zonk :: Terms tm => Env -> tm -> Either Error tm
zonk env tm = case runM (unZonk (zonk' tm)) env Set.empty of
  Right (a,_) -> Right a
  Left err    -> Left err

zonkVar :: Var -> Zonk Term
zonkVar v =
  do env  <- Zonk ask
     seen <- Zonk get
     let i = varIndex v
     case Map.lookup i env of
       Just tm' | Set.member i seen -> Zonk (raise (OccursCheckFailed (TVar v) tm'))
                | otherwise         -> do Zonk (set (Set.insert i seen))
                                          zonk' tm'
       Nothing                      -> return (TVar v)

class Terms tm where
  zonk' :: tm -> Zonk tm

instance Terms tm => Terms [tm] where
  zonk' = mapM zonk'

instance Terms Term where
  zonk' = go
    where
    go (TApp l r) =
      do l' <- go l
         r' <- go r
         return (TApp l' r')

    go (TVar v) = zonkVar v

    go tm =
      return tm

instance Terms Operator where
  zonk' op =
    do pre  <- zonk' (oPrecond  op)
       post <- zonk' (oPostcond op)
       return op { oPrecond  = pre
                 , oPostcond = post }
