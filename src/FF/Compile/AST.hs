{-# LANGUAGE DeriveFunctor #-}

module FF.Compile.AST where

import qualified Data.Text as T


data Domain = Domain { domName      :: !T.Text
                     , domOperators :: [Operator]
                     } deriving (Show)

data Problem = Problem { probDomain :: !T.Text
                       , probObjects:: [Object]
                       , probInit   :: [Term]
                       , probGoal   :: [Effect]
                       } deriving (Show)

data Operator = Operator { opName    :: !T.Text
                         , opDerived :: !Bool
                         , opParams  :: [Param]
                         , opPrecond :: [Term]
                         , opEffects :: [Effect]
                         } deriving (Show)

type Name = T.Text

type Type = T.Text

data Typed a = Typed { tValue :: a
                     , tType  :: !Type
                     } deriving (Show,Eq,Ord)

type Param  = Typed Name
type Object = Typed Name

data Term = TAnd    [Term]
          | TOr     [Term]
          | TNot    !Term
          | TImply  !Term   !Term
          | TExists [Param] !Term
          | TForall [Param] !Term
          | TAtom   !Atom
            deriving (Show)

type Effect = Term

data Atom = Atom !Name [Arg]
            deriving (Show)

data Arg = AName !Name
         | AVar  !Name
           deriving (Show,Eq,Ord)
