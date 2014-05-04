module Types where

import           Control.Monad ( guard )
import           Data.Function ( on )
import qualified Data.Map as Map
import qualified Data.Set as Set


data Pred = Pred Bool String [Term]
            deriving (Eq,Show,Ord)

data Term = TVar Var
          | TGen Var
          | TCon String
            deriving (Eq,Show,Ord)

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Show)

instance Eq Var where
  (==) = (==) `on` varIndex
  (/=) = (/=) `on` varIndex

instance Ord Var where
  compare = compare `on` varIndex

-- | Negate a predicate.
tmNot :: Pred -> Pred
tmNot (Pred n p ts) = Pred (not n) p ts


-- Operators -------------------------------------------------------------------

type Operators = [Schema Operator]

data Operator = Operator { oName     :: String
                         , oPrecond  :: [Pred]
                         , oPostcond :: [Pred]
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

instance Inst Pred where
  inst as (Pred neg p ts) = Pred neg p (inst as ts)

instance Inst Term where
  inst as (TGen v) = as !! varIndex v
  inst _  tm         = tm

instance Inst Operator where
  inst as op = op { oPrecond  = inst as (oPrecond  op)
                  , oPostcond = inst as (oPostcond op) }


-- Plans -----------------------------------------------------------------------

type Domain = [Schema Operator]

data Step = Step { sName     :: String
                 , sPrecond  :: [Term]
                 , sPostcond :: [Term]
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

data SubGoal = SubGoal { sgStepId :: !StepId
                       , sgTerm   :: Term
                       } deriving (Show,Eq,Ord)

data Plan = Plan { planSteps :: Map.Map StepId Step
                   -- ^ The steps
                 , planSubGoals :: Set.Set SubGoal
                   -- ^ Open constraints to be resolved.
                 , planOpenSteps :: Set.Set StepId
                   -- ^ Steps with open preconditions
                 , planConstraints :: Set.Set Constraint
                   -- ^ Ordering constraints between steps
                 , planLinks :: Set.Set CausalLink
                   -- ^ Causal links between steps
                 , planNextStepId :: !Int
                   -- ^ The next available step identifier
                 } deriving (Show)

emptyPlan :: Assumps -> Goals -> Plan
emptyPlan assumps goals =
  Plan { planSteps       = Map.fromList [ (StartId, startStep)
                                        , (FinishId, finishStep) ]
       , planSubGoals    = Set.fromList (map mkSubGoal goals)
       , planOpenSteps   = Set.fromList [FinishId]
       , planConstraints = Set.fromList [StartId `Before` FinishId]
       , planLinks       = Set.empty
       , planNextStepId  = 0
       }
  where
  -- the start step asserts all assumptions as post-conditions.
  startStep  = Step { sName     = "<start>"
                    , sPrecond  = []
                    , sPostcond = assumps }

  -- the finish step has only open preconditions, the goals of the plan.
  finishStep = Step { sName     = "<finish>"
                    , sPrecond  = []
                    , sPostcond = [] }

  mkSubGoal g = SubGoal { sgStepId = FinishId
                        , sgTerm   = g }
