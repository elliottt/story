{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}

module FF.Compile where

import           FF.ConnGraph ( ConnGraph )
import qualified Planner.Constraints as CSP
import qualified Planner.DiscTrie as DT
import           Planner.Monad
import           Planner.Types
import           Pretty

import           Control.Monad ( foldM )
import           Data.Array ( listArray )
import qualified Data.Set as Set


compile assumps dom =
  do cg <- mkConnGraph effects
     mapM_ (print . pp) effects
  where
  dom'  = DT.mkDomain dom
  facts = DT.mkFacts [ assump | assump <- assumps
                              , DT.isRigid dom' assump ]

  effects = concat
          $ findAll facts dom'
          $ mapM instOperator dom


data Oper = Oper { oName   :: String
                 , oActors :: [Term]
                 , oVars   :: [Term]
                 , oPre    :: [Pred]
                 , oEff    :: [Effect]
                 } deriving (Show)

instance PP Oper where
  pp Oper { .. } =
    hang (text oName <+> parens (commas (map pp oVars)))
       2 $ text "actors:" <+> commas (map pp oActors)
        $$ text "pre:   " <+> commas (map pp oPre)
        $$ text "eff:   " <+> commas (map pp oEff)

instOperator :: Schema Action -> PlanM Oper
instOperator (Forall vs a) =
  do as <- mapM fresh vs
     let act = inst as a
     bs  <- foldM (flip CSP.constrain) CSP.empty (aConstraints act)
     bs' <- CSP.solve bs
     return Oper { oName   = aName act
                 , oActors = CSP.subst bs' (aActors act)
                 , oVars   = CSP.subst bs' as
                 , oPre    = CSP.subst bs' (aPrecond act)
                 , oEff    = CSP.subst bs' (aEffect act)
                 }

mkConnGraph :: [Oper] -> IO ConnGraph
mkConnGraph os =
  do mapM_ (print . pp) (Set.toList facts)
     undefined
  where
  facts = Set.fromList [ f | Oper { .. } <- os
                           , f <- map EPred oPre ++ oEff
                           , isAdd f ]

  isAdd (EPred (Pred n _ _)) = n
  isAdd _                    = True
