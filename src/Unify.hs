{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Unify (
    Env
  , Error
  , Zonk(), zonk
  , Unify(), mgu, match
  ) where

import Types

import           Control.Applicative
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Traversable ( traverse )
import           MonadLib

import Debug.Trace


-- External Interface ----------------------------------------------------------

-- | Variable environment.
type Env = Map.Map Var Term

data Error = UnificationFailed
           | MatchingFailed
           | OccursCheckFailed Term Term
             deriving (Show)

mgu :: Unify a => Env -> a -> a -> Either Error Env
mgu env a a' = case runUnifyM env (mgu' a a') of
                 Right (_,RW { .. }) -> Right rwEnv
                 Left err            -> Left err

match :: Unify a => Env -> a -> a -> Either Error Env
match env a a' = case runUnifyM env (match' a a') of
                   Right (_,RW { .. }) -> Right rwEnv
                   Left err            -> Left err

-- | Remove variables from term.
zonk :: Zonk a => Env -> a -> Either Error a
zonk env a = case runUnifyM env (zonk' a) of
               Right (a,_) -> Right a
               Left err    -> Left err

-- Unification Monad -----------------------------------------------------------

data RW = RW { rwSeen :: Set.Set Var
             , rwEnv  :: Env
             }

newtype UnifyM a = UnifyM { unUnifyM :: StateT RW (ExceptionT Error Id) a
                          } deriving (Functor,Applicative,Monad)

instance ExceptionM UnifyM Error where
  raise e = UnifyM (raise e)

runUnifyM :: Env -> UnifyM a -> Either Error (a,RW)
runUnifyM env m = runM (unUnifyM m) RW { rwSeen = Set.empty, rwEnv = env }

bindVar :: Var -> Term -> UnifyM (Maybe Term)
bindVar i tm = UnifyM $
  do rw <- get
     case Map.lookup i (rwEnv rw) of
       Just tm' -> return (Just tm')
       Nothing  -> do set rw { rwEnv = Map.insert i tm (rwEnv rw) }
                      return Nothing

seenVar :: Var -> UnifyM ()
seenVar v = UnifyM $ do rw <- get
                        set rw { rwSeen = Set.insert v (rwSeen rw) }

-- | Replace a variable with its binding.
zonkVar :: Var -> UnifyM Term
zonkVar v =
  do RW { .. } <- UnifyM get
     case Map.lookup v rwEnv of
       Just tm' | Set.member v rwSeen -> raise (OccursCheckFailed (TVar v) tm')
                | otherwise           -> do seenVar v
                                            zonk' tm'
       Nothing                        -> return (TVar v)


-- Primitive Unification -------------------------------------------------------

class Zonk a where
  zonk'  :: a -> UnifyM a

instance Zonk a => Zonk [a] where
  zonk' = traverse zonk'

instance (Zonk a, Zonk b) => Zonk (a,b) where
  zonk' (a,b) = do a' <- zonk' a
                   b' <- zonk' b
                   return (a',b')

instance Zonk Operator where
  zonk' (Operator n ps qs) =
    do oPrecond  <- zonk' ps
       oPostcond <- zonk' qs
       return Operator { oName = n, .. }

instance Zonk Pred where
  zonk' (Pred n p args) = Pred n p `fmap` zonk' args

instance Zonk Term where
  zonk' tm = case tm of
    TVar v -> do rw <- UnifyM get
                 case Map.lookup v (rwEnv rw) of
                   Just tm' -> zonk' tm'
                   Nothing  -> return tm
    _      -> return tm


class Zonk a => Unify a where
  mgu'   :: a -> a -> UnifyM ()
  match' :: a -> a -> UnifyM ()

instance Unify a => Unify [a] where
  mgu' (a:as) (b:bs) = do mgu' a b
                          mgu' as bs
  mgu' _      _      = raise UnificationFailed

  match' (a:as) (b:bs) = do match' a b
                            match' as bs
  match' []     []     = return ()
  match' _      _      = raise MatchingFailed

instance (Unify a, Unify b) => Unify (a,b) where
  mgu' (a,b) (c,d) = do mgu' a c
                        mgu' b d

  match' (a,b) (c,d) = do match' a c
                          match' b d

instance Unify Pred where
  mgu' (Pred n1 p1 args1) (Pred n2 p2 args2)
    | n1 == n2 && p1 == p2 =
      mgu' args1 args2

    | otherwise =
      raise UnificationFailed

  match' a@(Pred n1 p1 args1) b@(Pred n2 p2 args2)
    | n1 == n2 && p1 == p2 =
      match' args1 args2

    | otherwise =
      raise MatchingFailed

instance Unify Term where
  -- generalized variables only unify with themselves
  mgu' (TGen v1) (TGen v2) | v1 == v2 = return ()

  -- constructors only unify with themselves
  mgu' (TCon c1) (TCon c2) | c1 == c2 = return ()

  mgu' (TVar v1) (TVar v2) | v1 == v2 = return ()

  mgu' (TVar v1) b =
    do mb <- bindVar v1 b
       case mb of
         Just a  -> mgu' a b
         Nothing -> return ()

  mgu' a (TVar v2) =
    do mb <- bindVar v2 a
       case mb of
         Just b  -> mgu' a b
         Nothing -> return ()

  mgu' _ _ = raise UnificationFailed


  -- generalized variables only unify with themselves
  match' (TGen v1) (TGen v2) | v1 == v2 = return ()

  -- constructors only unify with themselves
  match' (TCon c1) (TCon c2) | c1 == c2 = return ()

  match' (TVar v1) (TVar v2) | v1 == v2 = return ()

  -- matching only allows variables to be instantiated on the LHS
  match' (TVar v1) b =
    do mb <- bindVar v1 b
       case mb of
         Just a  -> match' a b
         Nothing -> return ()

  match' _ _ = raise MatchingFailed
