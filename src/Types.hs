module Types where

import           Control.Monad ( guard )
import qualified Data.Map as Map
import qualified Data.Set as Set


data Term = TCon String
          | TVar Var
          | TBound Var
          | TApp Term Term
            deriving (Eq,Show,Ord)

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Eq,Show,Ord)

tmApp :: Term -> [Term] -> Term
tmApp f xs = foldl TApp f xs

-- | Negate a term.
tmNot :: Term -> Term
tmNot tm = tmApp (TCon "not") [tm]


-- Operators -------------------------------------------------------------------

type Operators = [Schema Operator]

data Operator = Operator { oName     :: String
                         , oPrecond  :: [Term]
                         , oPostcond :: [Term]
                         } deriving (Show,Eq,Ord)


-- Schemas ---------------------------------------------------------------------

data Schema a = Forall [Var] a
                deriving (Show)

instSchema :: Inst a => [Term] -> Schema a -> Maybe a
instSchema ts (Forall vs a) =
  do guard (length ts == length vs)
     return (inst ts a)


-- | Instantiate the bound variables in a term.
class Inst a where
  inst :: [Term] -> a -> a

instance Inst a => Inst [a] where
  inst as = map (inst as)

instance Inst Term where
  inst as (TApp l r) = TApp (inst as l) (inst as r)
  inst as (TBound v) = as !! varIndex v
  inst _  tm         = tm

instance Inst Operator where
  inst as op = op { oPrecond  = inst as (oPrecond  op)
                  , oPostcond = inst as (oPostcond op) }


-- Plans -----------------------------------------------------------------------

data Step = Step { sName        :: String
                 , sOpenPrecond :: [Term]
                 , sPrecond     :: [Term]
                 , sPostcond    :: [Term]
                 } deriving (Show)

-- | Step a must come before step b.
data Constraint = Before StepId StepId
                  deriving (Show,Eq,Ord)

-- | Causal links: between steps a and b, condition c is protected.
data CausalLink = Link StepId Term StepId
                  deriving (Show,Eq,Ord)

type Assumps = [Term]

type Goals = [Term]

data StepId = StartId     -- ^ Unique id for the starting step
            | StepId !Int -- ^ Generic step ids
            | FinishId    -- ^ Unique id for the ending step
              deriving (Show,Eq,Ord)

data Plan = Plan { planSteps       :: Map.Map StepId Step
                   -- ^ The steps
                 , planOpenSteps   :: Set.Set StepId
                   -- ^ Steps with open preconditions
                 , planConstraints :: Set.Set Constraint
                   -- ^ Ordering constraints between steps
                 , planLinks       :: Set.Set CausalLink
                   -- ^ Causal links between steps
                 , planNextStepId  :: !Int
                   -- ^ The next available step identifier
                 } deriving (Show)

emptyPlan :: Assumps -> Goals -> Plan
emptyPlan assumps goals =
  Plan { planSteps       = Map.fromList [ (StartId, startStep)
                                        , (FinishId, finishStep) ]
       , planOpenSteps   = Set.fromList [ FinishId ]
       , planConstraints = Set.fromList [StartId `Before` FinishId]
       , planLinks       = Set.empty
       , planNextStepId  = 0
       }
  where
  -- the start step asserts all assumptions as post-conditions.
  startStep  = Step { sName        = "<start>"
                    , sOpenPrecond = []
                    , sPrecond     = []
                    , sPostcond    = assumps }

  -- the finish step has only open preconditions, the goals of the plan.
  finishStep = Step { sName        = "<finish>"
                    , sOpenPrecond = goals
                    , sPrecond     = []
                    , sPostcond    = [] }
