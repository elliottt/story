{-# LANGUAGE DeriveFunctor #-}

module FF.Compile.AST where

import qualified Data.Text as T


data Domain = Domain { domName      :: !T.Text
                     , domOperators :: [Operator]
                     } deriving (Show)

data Problem = Problem { probDomain :: !T.Text
                       , probInit   :: [Term]
                       , probGoal   :: [Effect]
                       } deriving (Show)

data Operator = Operator { opName    :: !T.Text
                         , opParams  :: [Param]
                         , opPrecond :: [Term]
                         , opEffects :: [Effect]
                         } deriving (Show)

type Name = T.Text

data Param = Param { pName :: !Name
                   , pType :: !Name
                   } deriving (Show)

data Quantify a = Quantify [Param] a
                  deriving (Show,Functor)

data Term = TAnd    [Term]
          | TOr     [Term]
          | TPred   !Term
          | TNot     Term
          | TImply   Term Term
          | TExists (Quantify Term)
          | TForall (Quantify Term)
          | TAtom   !Atom
            deriving (Show)

type Effect = Term

data Atom = Atom !Name [Name]
            deriving (Show)
