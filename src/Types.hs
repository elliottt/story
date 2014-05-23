{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Types where

import Pretty

import           Control.Monad ( guard )
import           Data.Function ( on )
import qualified Data.Map as Map
import           Data.String ( IsString(..) )
import qualified Data.Set as Set


data Pred = Pred Bool String [Term]
            deriving (Eq,Show,Ord)

instance PP Pred where
  pp (Pred b n ts) = ppNeg <> text n <> parens (commas (map pp ts))
    where
    ppNeg | b         = empty
          | otherwise = char '~'

predName :: Pred -> String
predName (Pred _ n _) = n

predDeletes :: Pred -> Bool
predDeletes (Pred b _ _) = b

predNegate :: Pred -> Pred
predNegate (Pred b p ts) = Pred (not b) p ts

data Term = TVar Var
          | TGen Var
          | TCon String
            deriving (Eq,Show,Ord)

instance PP Term where
  pp (TVar v) = char '?' <> pp v
  pp (TGen v) =             pp v
  pp (TCon c) = text c

instance IsString Term where
  fromString = TCon

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Show)

instance PP Var where
  pp Var { varDisplay = Just str } = text str
  pp Var { varIndex   = ix       } = char 'v' <> int ix

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

instance PP Operator where
  pp Operator { .. } = text oName
                    <> parens (pp oPrecond $$ text "=>" $$ pp oPostcond)


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

-- | Causal links: between steps a and b, condition c is protected.
data CausalLink = Link { clLeft  :: Action
                       , clPred  :: Pred
                       , clRight :: Action
                       } deriving (Show,Eq,Ord)

instance PP CausalLink where
  pp (Link l p r) = pp l <+> char '-' <> braces (pp p) <> text "->" <+> pp r

type Assumps = [Pred]

type Goals = [Pred]

data Action = Start
            | Inst Int String [Term]
            | Finish
              deriving (Show)

instance PP Action where
  pp Start         = text "Start"
  pp (Inst i n ts) = text n <> braces (int i) <> parens (commas (map pp ts))
  pp Finish        = text "Finish"

instance Eq Action where
  Start      == Start      = True
  Inst a _ _ == Inst b _ _ = a == b
  Finish     == Finish     = True
  _          == _          = False

instance Ord Action where
  compare Inst{}       Start        = GT
  compare (Inst a _ _) (Inst b _ _) = compare a b
  compare Inst{}       Finish       = LT

  compare Start        Start        = EQ
  compare Start        _            = LT

  compare Finish       Finish       = EQ
  compare Finish       _            = GT
