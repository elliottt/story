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

  prob = Problem { probInit = [ TAtom initAtom ]
                 , probGoal = [ TAtom goalAtom ]
                 , ..
                 }

  ops  = [ Operator { opName    = "$init-operator"
                    , opParams  = []
                    , opPrecond = [ TAtom initAtom ]
                    , opEffects = TNot (TAtom initAtom) : probInit
                    }

         , Operator { opName    = "$goal-operator"
                    , opParams  = []
                    , opPrecond = probGoal
                    , opEffects = [ TAtom goalAtom ]
                    }
         ]
