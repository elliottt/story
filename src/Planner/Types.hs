{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}

module Planner.Types where

import Pretty

import           Control.Monad ( guard )
import           Data.Function ( on )
import           Data.Foldable ( foldMap )
import           Data.String ( IsString(..) )
import qualified Data.Set as Set


-- Terms -----------------------------------------------------------------------

data Constraint = CPred Pred
                | CNeq Term Term
                  deriving (Show,Eq,Ord)

data Effect = EPred Pred
            | EIntends Actor Pred
              deriving (Show,Eq,Ord)

data Pred = Pred { pNeg  :: Bool
                 , pSym  :: String
                 , pArgs :: [Term]
                 } deriving (Show,Eq,Ord)

negPred :: Pred -> Pred
negPred p = p { pNeg = not (pNeg p) }

type Type = Term

data Term = TVar Var
          | TGen Var
          | TCon String
            deriving (Eq,Show,Ord)

instance IsString Term where
  fromString = TCon

instance Num Term where
  fromInteger n = TVar (Var Nothing (fromInteger n))

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Show)

instance Eq Var where
  (==) = (==) `on` varIndex
  (/=) = (/=) `on` varIndex

instance Ord Var where
  compare = compare `on` varIndex


type Actor = Term

data Action = Action { aName        :: String
                     , aActors      :: [Actor]
                     , aHappening   :: Bool
                     , aConstraints :: [Constraint]
                     , aPrecond     :: [Pred]
                     , aEffect      :: [Effect]
                     } deriving (Show,Eq,Ord)

emptyAction :: Action
emptyAction  = Action { aName        = ""
                      , aActors      = []
                      , aHappening   = False
                      , aConstraints = []
                      , aPrecond     = []
                      , aEffect      = [] }


-- Variables -------------------------------------------------------------------

isGround :: Vars a => a -> Bool
isGround a = Set.null (vars a)

class Vars a where
  vars :: a -> Set.Set Var

instance Vars a => Vars [a] where
  vars = foldMap vars

instance Vars a => Vars (Set.Set a) where
  vars = foldMap vars

instance Vars a => Vars (Maybe a) where
  vars = foldMap vars

instance Vars Pred where
  vars Pred { .. } = vars pArgs

instance Vars Term where
  vars (TVar  v) = Set.singleton v
  vars (TGen  _) = Set.empty
  vars (TCon  _) = Set.empty


-- Schemas ---------------------------------------------------------------------

data Schema a = Forall [Var] a
                deriving (Show,Functor)

forall :: [String] -> ([Term] -> a) -> Schema a
forall ts mkBody = Forall vs (mkBody (map TGen vs))
  where
  vs = [ Var (Just t) i | i <- [ 0 .. ]
                        | t <- ts ]

instSchema :: Inst a => [Term] -> Schema a -> Maybe a
instSchema ts (Forall vs a) =
  do guard (length ts == length vs)
     return (inst ts a)


-- | Instantiate the bound variables in a term.
class Inst a where
  inst :: [Term] -> a -> a

instance (Inst a, Inst b) => Inst (a,b) where
  inst as (a,b) = (inst as a, inst as b)

instance Inst a => Inst [a] where
  inst as = map (inst as)

instance Inst Constraint where
  inst as (CPred p)  = CPred (inst as p)
  inst as (CNeq a b) = CNeq (inst as a) (inst as b)

instance Inst Effect where
  inst as (EPred p)      = EPred (inst as p)
  inst as (EIntends a p) = EIntends (inst as a) (inst as p)

instance Inst Pred where
  inst as p = p { pArgs = inst as (pArgs p) }

instance Inst Term where
  inst as (TGen v) = as !! varIndex v
  inst _  tm       = tm

instance Inst Action where
  inst as act = act { aActors      = inst as (aActors  act)
                    , aConstraints = inst as (aConstraints act)
                    , aPrecond     = inst as (aPrecond act)
                    , aEffect      = inst as (aEffect  act) }


-- Plans -----------------------------------------------------------------------

type Domain = [Schema Action]

-- | Causal links: between steps a and b, condition c is protected.
data Link = Link { clLeft  :: Step
                 , clPred  :: Pred
                 , clRight :: Step
                 } deriving (Show,Eq,Ord)

-- | Frames of commitment.
data Frame = Frame { fSteps :: Set.Set Step
                   , fActor :: Actor
                   , fGoal  :: Pred
                   , fFinal :: Step
                   , fMotivation :: Maybe Step
                   } deriving (Show,Eq,Ord)

allSteps :: Frame -> Set.Set Step
allSteps Frame { .. } = Set.insert fFinal fSteps

type Assumps = [Effect]

type Goals = [Pred]

data Step = Start
          | Inst Int String [Term]
          | Finish
            deriving (Show)

instance Eq Step where
  Start      == Start      = True
  Inst a _ _ == Inst b _ _ = a == b
  Finish     == Finish     = True
  _          == _          = False

instance Ord Step where
  compare Inst{}       Start        = GT
  compare (Inst a _ _) (Inst b _ _) = compare a b
  compare Inst{}       Finish       = LT

  compare Start        Start        = EQ
  compare Start        _            = LT

  compare Finish       Finish       = EQ
  compare Finish       _            = GT


-- Pretty-printing -------------------------------------------------------------

instance PP Frame where
  pp Frame { .. } =
    angles $ commas [ brackets (commas (map pp (Set.toList fSteps)))
                    , pp fActor
                    , pp fGoal
                    , pp fFinal
                    , maybe (text "<no motivation>") pp fMotivation ]

instance PP Pred where
  pp Pred { .. } = ppNeg <> text pSym <> parens (commas (map pp pArgs))
    where
    ppNeg | pNeg      = empty
          | otherwise = char '~'

instance PP Term where
  pp (TVar v) = char '?' <> pp v
  pp (TGen v) =             pp v
  pp (TCon c) = text c

instance PP Var where
  pp Var { varDisplay = Just str } = text str
  pp Var { varIndex   = ix       } = char 'v' <> int ix

instance PP Constraint where
  pp (CPred p)  = pp p
  pp (CNeq a b) = pp a <+> text "<>" <+> pp b

instance PP Effect where
  pp (EPred p)      = pp p
  pp (EIntends a p) = text "intends" <> parens (commas [pp a, pp p])

instance PP Action where
  pp Action { .. } = text aName
                  <> parens (pp aPrecond $$ text "=>" $$ pp aEffect)

instance PP Step where
  pp Start         = text "Start"
  pp (Inst i n ts) = text n <> braces (int i) <> parens (commas (map pp ts))
  pp Finish        = text "Finish"

instance PP Link where
  pp (Link l p r) = pp l <+> char '-' <> braces (pp p) <> text "->" <+> pp r
