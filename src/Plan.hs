{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Plan where

import           Types
import qualified Unify

import           Data.Monoid ( mempty )
import qualified Data.Set as Set
import           MonadLib




-- Planning Monad --------------------------------------------------------------

newtype PlanM a = PlanM { unPlanM :: StateT RW (ChoiceT Id) a
                        } deriving (Functor,Monad,MonadPlus)

data RW = RW { rwFresh :: Int
             , rwEnv   :: Unify.Env
             }

runPlanM :: PlanM a -> Maybe a
runPlanM m = fmap fst (runId (findOne (runStateT rw (unPlanM m))))
  where
  rw = RW { rwFresh = 0
          , rwEnv   = mempty
          }

getEnv :: PlanM Unify.Env
getEnv  = PlanM (rwEnv `fmap` get)

fresh :: Var -> PlanM Term
fresh v = PlanM $ do rw <- get
                     set rw { rwFresh = rwFresh rw + 1 }
                     return (TVar v { varIndex = rwFresh rw })

fresh_ :: PlanM Term
fresh_  = fresh (Var Nothing 0)

freshInst :: Inst a => Schema a -> PlanM a
freshInst (Forall vs a) =
  do ts <- mapM fresh vs
     return (inst ts a)

match :: Term -> Term -> PlanM ()
match l r = PlanM $
  do rw <- get
     case Unify.match (rwEnv rw) l r of
       Right env' -> set rw { rwEnv = env' }
       Left _     -> mzero

unify :: Term -> Term -> PlanM ()
unify l r = PlanM $
  do rw <- get
     case Unify.mgu (rwEnv rw) l r of
       Right env' -> set rw { rwEnv = env' }
       Left _     -> mzero

zonk :: Unify.Terms tm => tm -> PlanM tm
zonk tm = PlanM $
  do rw <- get
     case Unify.zonk (rwEnv rw) tm of
       Right tm' -> return tm'
       Left _    -> mzero

-- | Return the instantiated action, and extended environment that achieves the
-- condition p.
achieves :: Schema Operator -> Term -> PlanM Operator
achieves op p =
  do iop <- freshInst op
     msum [ match c p >> zonk iop | c <- oPostcond iop ]


-- Testing ---------------------------------------------------------------------

test = Forall [a,b] Operator
  { oName     = "test"
  , oPrecond  = []
  , oPostcond = [tmApp (TCon "At") [TBound a, TBound b]]
  }
  where
  a = Var (Just "a") 0
  b = Var (Just "b") 1
