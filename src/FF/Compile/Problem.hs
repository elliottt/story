{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module FF.Compile.Problem where

import FF.Compile.AST


-- | Generate operators from the problem description.  This corresponds to the
-- "Initial Conditions and Goals" section.
genProblemOperators :: Problem -> (Problem, [Operator])
genProblemOperators Problem { .. } = (prob, ops)
  where

  initAtom = Atom "$init-problem"  []
  goalAtom = Atom "$goal-achieved" []

  prob = Problem { probInit = [LAtom initAtom]
                 , probGoal = TAtom goalAtom
                 , ..
                 }

  ops  = [ Operator { opName    = "$init-operator"
                    , opDerived = True
                    , opParams  = []
                    , opPrecond = TAtom initAtom
                    , opEffects = EPrim (LNot initAtom : probInit)
                    }

         , Operator { opName    = "$goal-operator"
                    , opDerived = True
                    , opParams  = []
                    , opPrecond = probGoal
                    , opEffects = EPrim [LAtom goalAtom]
                    }
         ]
