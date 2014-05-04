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
data Constraint = Action :< Action
                  deriving (Show,Eq,Ord)

-- | Causal links: between steps a and b, condition c is protected.
data CausalLink = Link Action Term Action
                  deriving (Show,Eq,Ord)

type Assumps = [Term]

type Goals = [Term]

data Action = Start
            | Inst Int String [Term]
            | Finish
              deriving (Show,Eq,Ord)
