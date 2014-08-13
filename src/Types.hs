{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Types where

import Pretty

import           Control.Monad ( guard )
import           Data.Function ( on )
import           Data.String ( IsString(..) )


-- Terms -----------------------------------------------------------------------

data Constraint = CNeq Term Term  -- ^ Inequality
                | CAssert Formula -- ^ Assertions about a term
                  deriving (Eq,Show,Ord)

data Pred = PFormula Formula         -- ^ A simple formula
          | PIntends Term Formula -- ^ A character intent
            deriving (Eq,Show,Ord)

predNegate :: Pred -> Pred
predNegate (PFormula p)     = PFormula (negFormula p)
predNegate (PIntends who p) = PIntends who (negFormula p)

data Formula = Formula { fNeg  :: Bool
                       , fSym  :: String 
                       , fArgs :: [Term]
                       } deriving (Show,Eq,Ord)

negFormula :: Formula -> Formula
negFormula p = p { fNeg = not (fNeg p) }

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
                     , aActors      :: [Term]
                     , aHappening   :: Bool
                     , aConstraints :: [Constraint]
                     , aPrecond     :: [Pred]
                     , aEffect      :: [Pred]
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

instance Inst Constraint where
  inst as (CNeq a b)  = CNeq (inst as a) (inst as b)
  inst as (CAssert p) = CAssert (inst as p)

instance Inst Pred where
  inst as (PFormula f)     = PFormula (inst as f)
  inst as (PIntends who p) = PIntends (inst as who) (inst as p)

instance Inst Formula where
  inst as form = form { fArgs = inst as (fArgs form) }

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

instance PP Constraint where
  pp (CNeq a b)  = pp a <+> text "/=" <+> pp b
  pp (CAssert p) = pp p

instance PP Pred where
  pp (PFormula p)     = pp p
  pp (PIntends who p) = text "intends" <> parens (pp who <> comma <+> pp p)

instance PP Formula where
  pp Formula { .. } = ppNeg <> text fSym <> parens (commas (map pp fArgs))
    where
    ppNeg | fNeg      = char '~'
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
