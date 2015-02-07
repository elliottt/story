{-# LANGUAGE DeriveFunctor #-}

module FF.Compile.AST where

import qualified Data.Text as T


data Domain = Domain { domName      :: !T.Text
                     , domOperators :: [Operator]
                     } deriving (Show)

data Problem = Problem { probDomain :: !T.Text
                       , probObjects:: [Object]
                       , probInit   :: [Literal]
                       , probGoal   :: Term
                       } deriving (Show)

data Operator = Operator { opName    :: !T.Text
                         , opDerived :: !Bool
                         , opParams  :: [Param]
                         , opPrecond :: Term
                         , opEffects :: Effect
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

mkTAnd :: [Term] -> Term
mkTAnd [t] = t
mkTAnd ts  = TAnd ts

data Effect = EForall [Param] Effect
            | EWhen Term [Literal]
            | EAnd [Effect]
            | EPrim [Literal]
              deriving (Show)

mkEWhen :: [Term] -> [Literal] -> Effect
mkEWhen [] = EPrim
mkEWhen ps = EWhen (mkTAnd ps)

data Literal = LAtom Atom
             | LNot  Atom
               deriving (Show)

data Atom = Atom !Name [Arg]
            deriving (Show)

data Arg = AName !Name
         | AVar  !Name
           deriving (Show,Eq,Ord)
