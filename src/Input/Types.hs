{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}

module Input.Types where

import           Data.Hashable (Hashable)
import qualified Data.Text as T
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import           GHC.Generics (Generic)


type Name = T.Text
type Var  = T.Text

data Term = TName !Name
          | TVar  !Var
            deriving (Eq,Ord,Generic,Show)

instance Hashable Term

-- | Types in the domain.
newtype Type = Type T.Text
               deriving (Eq,Ord,Generic,Show)

instance Hashable Type

data Typed a = Typed !a !Type
               deriving (Generic,Show)

instance Hashable a => Hashable (Typed a)

-- | A constant, and its type.
type Constant = Typed Name

-- | The story domain.
data Domain =
  Domain { domName :: !T.Text
           -- ^ The name of this domain

         , domTypes :: ![Type]
           -- ^ Types managed by the domain

         , domConsts :: ![Constant]
           -- ^ Domain-defined constants

         , domProperties :: ![PredDef]
           -- ^ Predicates that are not allowed to show up in the effects part
           -- of an action.

         , domPreds :: ![PredDef]
           -- ^ Predicate definitions

         , domActions :: ![Action]
           -- ^ Domain actions
         } deriving (Show)

-- type PredDef = Pred (Typed Name)

-- | The definition of a predicate.
data PredDef =
  PredDef { pdName :: !T.Text
            -- ^ The name of the predicate.

          , pdSpec :: [Typed T.Text]
            -- ^ The arguments to the predicate, with their types.
          } deriving (Show)

-- | Predicate instantiations, applied to a list of arguments.
data Pred arg =
  Pred { predName :: !T.Text
         -- ^ The name of the predicate

       , predArgs :: [arg]
         -- ^ Arguments to the predicate (names or variables)
       } deriving (Eq,Ord,Show,Generic)

instance Hashable arg => Hashable (Pred arg)

type Param = Typed T.Text

data Action =
  Action { actName :: !T.Text
           -- ^ Action name

         , actParams :: ![Param]
           -- ^ Typed parameters

         , actPrecond :: !Pre
           -- ^ Preconditions

         , actEffect :: !Effect
           -- ^ Effects
         } deriving (Show)


data Pre = PAnd ![Pre]
         | POr  ![Pre]
         | PNot !Pre
         | PImp !Pre !Pre
         | PExists ![Typed T.Text] !Pre
         | PForall ![Typed T.Text] !Pre
         | PLit    !Literal
           deriving (Show)

elimPAnd :: Pre -> [Pre]
elimPAnd (PAnd ps) = ps
elimPAnd p         = [p]

pAnd :: [Pre] -> Pre
pAnd [p] = p
pAnd ps  = PAnd (concatMap elimPAnd ps)

elimPOr :: Pre -> [Pre]
elimPOr (POr ps) = ps
elimPOr p        = [p]

pOr :: [Pre] -> Pre
pOr [p] = p
pOr ps  = POr (concatMap elimPOr ps)

data Effect = EForall ![Typed T.Text] Effect
            | EWhen !Pre !Effect
            | EAnd ![Effect]
            | ENot !Literal
            | ELit !Literal
              deriving (Show)

elimEAnd :: Effect -> [Effect]
elimEAnd (EAnd es) = es
elimEAnd e         = [e]

eAnd :: [Effect] -> Effect
eAnd [e] = e
eAnd es  = EAnd (concatMap elimEAnd es)


-- | Problem description.
data Problem dom =
  Problem { probName :: !T.Text

          , probDomain :: !dom
            -- ^ The domain to use when processing this problem.

          , probObjects :: ![Constant]
            -- ^ Objects introduced by the problem
            --
            -- NOTE: the types of the constants must be defined by the domain

          , probInit :: ![Literal]
            -- ^ The initial state of the problem.

          , probGoal :: !Pre
            -- ^ The goal state of the problem.
          } deriving (Show)

-- | Predicates instantiated with constant values.
type Literal = Pred Name


-- | All constants from the domain and the problem definition, indexed by their
-- type.
problemObjects :: Problem Domain -> HM.HashMap Type (HS.HashSet T.Text)
problemObjects Problem { probDomain = Domain { domConsts }, probObjects } =
  foldMap mkEntry (probObjects ++ domConsts)
  where
  mkEntry (Typed obj ty) = HM.singleton ty (HS.singleton obj)
