{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Types where

import Pretty

import           Control.Monad ( guard )
import           Data.Function ( on )
import           Data.String ( IsString(..) )
import qualified Data.Set as Set


-- Terms -----------------------------------------------------------------------

data Effect = EPred Pred
            | EIntends Term Pred
              deriving (Show,Eq,Ord)

data Pred = Pred { pNeg  :: Bool
                 , pSym  :: String 
                 , pArgs :: [Term]
                 } deriving (Show,Eq,Ord)

negPred :: Pred -> Pred
negPred p = p { pNeg = not (pNeg p) }

data Const = CNeq Term Term -- ^ Inequality
           | CPred Pred     -- ^ Typing predicates
             deriving (Show,Eq,Ord)

type Type = Term

type Actor = Term

data Term = TVar Var
          | TGen Var
          | TCon String
            deriving (Eq,Show,Ord)

instance IsString Term where
  fromString = TCon

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Show)

instance Eq Var where
  (==) = (==) `on` varIndex
  (/=) = (/=) `on` varIndex

instance Ord Var where
  compare = compare `on` varIndex


data Action = Action { aName        :: String
                     , aActors      :: [Actor]
                     , aHappening   :: Bool
                     , aConstraints :: [Const]
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


-- Schemas ---------------------------------------------------------------------

data Schema a = Forall [Var] a
                deriving (Show)

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

instance Inst a => Inst [a] where
  inst as = map (inst as)

instance Inst Effect where
  inst as (EPred f)        = EPred    (inst as f)
  inst as (EIntends who p) = EIntends (inst as who) (inst as p)

instance Inst Pred where
  inst as p = p { pArgs = inst as (pArgs p) }

instance Inst Term where
  inst as (TGen v) = as !! varIndex v
  inst _  tm         = tm

instance Inst Action where
  inst as act = act { aPrecond = inst as (aPrecond act)
                    , aEffect  = inst as (aEffect  act) }


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
                   , fGoal  :: Term
                   , fFinal :: Step
                   } deriving (Show,Eq,Ord)

type Assumps = [Pred]

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

instance PP Effect where
  pp (EPred p)        = pp p
  pp (EIntends who p) = text "intends" <> parens (pp who <> comma <+> pp p)

instance PP Pred where
  pp Pred { .. } = ppNeg <> text pSym <> parens (commas (map pp pArgs))
    where
    ppNeg | pNeg      = char '~'
          | otherwise = empty

instance PP Term where
  pp (TVar v) = char '?' <> pp v
  pp (TGen v) =             pp v
  pp (TCon c) = text c

instance PP Var where
  pp Var { varDisplay = Just str } = text str
  pp Var { varIndex   = ix       } = char 'v' <> int ix

instance PP Action where
  pp Action { .. } = text aName
                  <> parens (pp aPrecond $$ text "=>" $$ pp aEffect)

instance PP Step where
  pp Start         = text "Start"
  pp (Inst i n ts) = text n <> braces (int i) <> parens (commas (map pp ts))
  pp Finish        = text "Finish"

instance PP Link where
  pp (Link l p r) = pp l <+> char '-' <> braces (pp p) <> text "->" <+> pp r
