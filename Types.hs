module Types where

data Term = TCon String
          | TVar Var
          | TBound Var
          | TApp Term Term
            deriving (Eq,Show)

data Var = Var { varDisplay :: Maybe String
               , varIndex   :: Int
               } deriving (Eq,Show,Ord)

app :: Term -> [Term] -> Term
app f xs = foldl TApp f xs


-- | Instantiate the bound variables in a term.
class Inst a where
  inst :: [Term] -> a -> a

instance Inst Term where
  inst as (TApp l r) = TApp (inst as l) (inst as r)
  inst as (TBound v) = as !! varIndex v
  inst _  tm         = tm
