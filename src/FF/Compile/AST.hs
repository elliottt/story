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
          | TLit    !Literal
            deriving (Show)

mkTAnd :: [Term] -> Term
mkTAnd [t] = t
mkTAnd ts  = TAnd ts

data Effect = EForall [Param] Effect
            | EWhen Term [Literal]
            | EAnd [Effect]
            | ELit Literal
              deriving (Show)

mkEWhen :: [Term] -> [Literal] -> Effect
mkEWhen [] = mkELitConj
mkEWhen ps = EWhen (mkTAnd ps)

mkELitConj :: [Literal] -> Effect
mkELitConj xs = EAnd (map ELit xs)

elimEAnd :: Effect -> [Effect]
elimEAnd (EAnd es) = concatMap elimEAnd es
elimEAnd e         = [e]

isELit :: Effect -> Bool
isELit ELit{} = True
isELit _      = False

data Literal = LAtom Atom
             | LNot  Atom
               deriving (Show)

data Atom = Atom !Name [Arg]
            deriving (Show,Eq,Ord)

data Arg = AName !Name
         | AVar  !Name
           deriving (Show,Eq,Ord)
