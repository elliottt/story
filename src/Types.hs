module Types where

import Control.Monad ( guard )


data Term = TCon String
          | TVar Var
          | TBound Var
          | TApp Term Term
            deriving (Eq,Show,Ord)

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Eq,Show,Ord)

tmApp :: Term -> [Term] -> Term
tmApp f xs = foldl TApp f xs

-- | Negate a term.
tmNot :: Term -> Term
tmNot tm = tmApp (TCon "not") [tm]


-- Actions ---------------------------------------------------------------------

type Actions = [Schema Action]

data Action = Action { aName     :: String
                     , aPrecond  :: [Term]
                     , aPostcond :: [Term]
                     } deriving (Show,Eq,Ord)


-- Schemas ---------------------------------------------------------------------

data Schema a = Forall [Var] a
                deriving (Show)

instSchema :: Inst a => [Term] -> Schema a -> Maybe a
instSchema ts (Forall vs a) =
  do guard (length ts == length vs)
     return (inst ts a)


-- | Instantiate the bound variables in a term.
class Inst a where
  inst :: [Term] -> a -> a

instance Inst a => Inst [a] where
  inst as = map (inst as)

instance Inst Term where
  inst as (TApp l r) = TApp (inst as l) (inst as r)
  inst as (TBound v) = as !! varIndex v
  inst _  tm         = tm

instance Inst Action where
  inst as act = act { aPrecond  = inst as (aPrecond act)
                    , aPostcond = inst as (aPostcond act) }
