module Input.Types where

import qualified Data.Text as T


-- | Types in the domain.
newtype Type = Type T.Text
               deriving (Show)

data Typed a = Typed !a !Type
               deriving (Show)

-- | A constant, and its type.
type Constant = Typed T.Text

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

-- | The definition of a predicate.
data PredDef =
  PredDef { pdName :: !T.Text
            -- ^ The name of the predicate.

          , pdSpec :: [Typed T.Text]
            -- ^ The arguments to the predicate, with their types.
          } deriving (Show)

-- | Predicate instantiations with negation, applied to a list of arguments.
data Pred arg =
  Pred { predNeg :: !Bool
         -- ^ True when the predicate is negated

       , predName :: !T.Text
         -- ^ The name of the predicate

       , predArgs :: [arg]
         -- ^ Arguments to the predicate (names or variables)
       } deriving (Show)

type Param = Typed T.Text

data Action =
  Action { actName :: !T.Text
           -- ^ Action name

         , actParams :: [Param]
           -- ^ Typed parameters

         , actPrecond :: Term
           -- ^ Preconditions

         , actEffect :: Effect
           -- ^ Effects
         } deriving (Show)


data Term = TAnd ![Term]
          | TOr  ![Term]
          | TNot !Term
          | TImp !Term !Term
          | TExists ![Typed T.Text] !Term
          | TForall ![Typed T.Text] !Term
          | TLit    !Literal
            deriving (Show)

elimTAnd :: Term -> [Term]
elimTAnd (TAnd ts) = ts
elimTAnd t         = [t]

tAnd :: [Term] -> Term
tAnd [t] = t
tAnd ts  = TAnd (concatMap elimTAnd ts)

elimTOr :: Term -> [Term]
elimTOr (TOr ts) = ts
elimTOr t        = [t]

tOr :: [Term] -> Term
tOr [t] = t
tOr ts  = TOr (concatMap elimTOr ts)

data Effect = EForall ![Typed T.Text] Effect
            | EWhen !Term !Effect
            | EAnd ![Effect]
            | ELit !Literal
              deriving (Show)


-- | Problem description.
data Problem dom =
  Problem { probName :: !T.Text

          , probDomain :: dom
            -- ^ The domain to use when processing this problem.

          , probObjects :: [Constant]
            -- ^ Objects introduced by the problem
            --
            -- NOTE: the types of the constants must be defined by the domain

          , probInit :: [Literal]
            -- ^ The initial state of the problem.

          , probGoal :: Term
            -- ^ The goal state of the problem.
          } deriving (Show)

-- | Predicates instantiated with constant values.
type Literal = Pred T.Text

