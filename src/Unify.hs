{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Unify (
    Env
  , Error
  , Zonk(..), zonk
  , Unify(..), mgu, match
  ) where

import Pretty
import Types

import           Control.Applicative ( (<$>), Applicative(..) )
import           Data.Graph ( SCC(..) )
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import           Data.Traversable ( traverse )
import           MonadLib


-- External Interface ----------------------------------------------------------

-- | Variable environment.
type Env = Map.Map Var Term

data Error = UnificationFailed
           | MatchingFailed
           | OccursCheckFailed Term Term
             deriving (Show)

instance PP Error where
  pp e = text (show e)

mgu :: Unify a => Env -> a -> a -> Either Error Env
mgu env a a' = case runUnifyM env (mgu' a a') of
                 Right (_,RW { .. }) -> Right rwEnv
                 Left err            -> Left err

-- | Matching unification, allowing variables on the left to bind.
match :: Unify a => Env -> a -> a -> Either Error Env
match env a a' = case runUnifyM env (match' a a') of
                   Right (_,RW { .. }) -> Right rwEnv
                   Left err            -> Left err

-- | Remove variables from term.
zonk :: Zonk a => Env -> a -> Either Error a
zonk env a = case runUnifyM env (zonk' a) of
               Right (a',_) -> Right a'
               Left err     -> Left err


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

lookupVar :: Var -> UnifyM (Maybe Term)
lookupVar i = UnifyM $
  do rw <- get
     return (Map.lookup i (rwEnv rw))

bindVar :: Var -> Term -> UnifyM ()
bindVar i tm =
  do tm' <- zonk' tm
     UnifyM $ do rw  <- get
                 set rw { rwEnv = Map.insert i tm' (rwEnv rw) }


-- Primitive Unification -------------------------------------------------------

class Zonk a where
  zonk'  :: a -> UnifyM a

instance Zonk a => Zonk (SCC a) where
  zonk' (AcyclicSCC a) = AcyclicSCC `fmap` zonk' a
  zonk' (CyclicSCC as) = CyclicSCC  `fmap` zonk' as

instance Zonk a => Zonk [a] where
  zonk' = traverse zonk'

instance Zonk a => Zonk (Maybe a) where
  zonk' = traverse zonk'

instance (Ord a, Zonk a) => Zonk (Set.Set a) where
  zonk' as = do as' <- traverse zonk' (Set.toList as)
                return (Set.fromList as')

instance (Ord k, Zonk k, Zonk a) => Zonk (Map.Map k a) where
  zonk' m = do m' <- traverse zonk' (Map.toList m)
               return (Map.fromList m')

instance (Zonk a, Zonk b) => Zonk (a,b) where
  zonk' (a,b) = do a' <- zonk' a
                   b' <- zonk' b
                   return (a',b')

instance (Zonk a, Zonk b, Zonk c) => Zonk (a,b,c) where
  zonk' (a,b,c) = do a' <- zonk' a
                     b' <- zonk' b
                     c' <- zonk' c
                     return (a',b',c')

instance Zonk Step where
  zonk' Start         = return Start
  zonk' (Inst i p ts) = Inst i p `fmap` zonk' ts
  zonk' Finish        = return Finish

instance Zonk Frame where
  zonk' (Frame a b c d e) =
    do fSteps      <- zonk' a
       fActor      <- zonk' b
       fGoal       <- zonk' c
       fFinal      <- zonk' d
       fMotivation <- zonk' e
       return Frame { .. }

instance Zonk Action where
  zonk' (Action aName as aHappening cs ps qs) =
    do aPrecond     <- zonk' ps
       aActors      <- zonk' as
       aConstraints <- zonk' cs
       aEffect      <- zonk' qs
       return Action { .. }

instance Zonk Pred where
  zonk' (Pred pNeg pSym ts) =
    do pArgs <- zonk' ts
       return Pred { .. }

instance Zonk Term where
  zonk' tm = case tm of

    TVar v ->
      do rw <- UnifyM get
         case Map.lookup v (rwEnv rw) of
           Just tm' -> zonk' tm'
           Nothing  -> return tm

    TPred p ->
      TPred <$> zonk' p

    _ ->
      return tm

instance Zonk Link where
  zonk' (Link l p r) = Link <$> zonk' l
                            <*> zonk' p
                            <*> zonk' r


class Zonk a => Unify a where
  mgu'   :: a -> a -> UnifyM ()
  match' :: a -> a -> UnifyM ()

instance Unify a => Unify [a] where
  mgu' (a:as) (b:bs) = do mgu' a b
                          mgu' as bs
  mgu' []     []     = return ()
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

  match' (Pred n1 p1 args1) (Pred n2 p2 args2)
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

  mgu' (TPred p) (TPred q) = mgu' p q

  -- unification variables bind in either direction
  mgu' (TVar v1) b =
    do mb <- lookupVar v1
       case mb of
         Just a  -> mgu' a b
         Nothing -> bindVar v1 b

  mgu' a (TVar v2) =
    do mb <- lookupVar v2
       case mb of
         Just b  -> mgu' a b
         Nothing -> bindVar v2 a

  mgu' _ _ = raise UnificationFailed


  -- generalized variables only unify with themselves
  match' (TGen v1) (TGen v2) | v1 == v2 = return ()

  -- constructors only unify with themselves
  match' (TCon c1) (TCon c2) | c1 == c2 = return ()

  match' (TVar v1) (TVar v2) | v1 == v2 = return ()

  match' (TPred p) (TPred q) = match' p q

  -- matching only allows variables to be instantiated on the LHS
  match' (TVar v1) b =
    do mb <- lookupVar v1
       case mb of
         Just a  -> match' a b
         Nothing -> bindVar v1 b

  match' a (TVar v2) =
    do mb <- lookupVar v2
       case mb of
         Just b  -> match' a b
         Nothing -> raise MatchingFailed

  match' _ _ = raise MatchingFailed
