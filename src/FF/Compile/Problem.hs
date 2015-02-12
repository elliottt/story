{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module FF.Compile.Problem where

import FF.Compile.AST


-- | Generate operators from the problem description.  This corresponds to the
-- "Initial Conditions and Goals" section.
genProblemOperators :: Problem -> (Problem, [Operator])
genProblemOperators Problem { .. } = (prob, ops)
  where

  initAtom =        Atom "$init-problem"  []
  goalAtom = LAtom (Atom "$goal-achieved" [])

  prob = Problem { probInit = [LAtom initAtom]
                 , probGoal = TLit goalAtom
                 , ..
                 }

  ops  = [ Operator { opName    = "$init-operator"
                    , opDerived = True
                    , opParams  = []
                    , opPrecond = TLit (LAtom initAtom)
                    , opEffects = mkELitConj (LNot initAtom : probInit)
                    }

         , Operator { opName    = "$goal-operator"
                    , opDerived = True
                    , opParams  = []
                    , opPrecond = probGoal
                    , opEffects = ELit goalAtom
                    }
         ]
