module Planner ( findPlan ) where

import qualified Planner.DiscTrie as D
import           Planner.IPOCL ( ipocl )
import           Planner.Monad ( runPlanM )
import           Planner.Types ( Domain, Assumps, Goals, Step )


findPlan :: Domain -> Assumps -> Goals -> Maybe [Step]
findPlan domain assumps goals = runPlanM facts dom (ipocl assumps goals)
  where
  dom   = D.mkDomain domain
  facts = D.mkFacts [ p | p <- assumps, D.isRigid dom p ]
