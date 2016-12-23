{-# LANGUAGE OverloadedStrings #-}

import FF.Compile
import FF.Planner

-- Testing ---------------------------------------------------------------------

testDom = Domain
  { domName      = "test"
  , domOperators =
    [ Operator { opName    = "opA1"
               , opDerived = False
               , opParams  = []
               , opPrecond = TAnd []
               , opEffects = ELit (LAtom (Atom "A" []))
               }
    , Operator { opName    = "opA2"
               , opDerived = False
               , opParams  = []
               , opPrecond = TLit (LAtom (Atom "A" []))
               , opEffects = ELit (LAtom (Atom "B" []))
               }
    , Operator { opName    = "foo"
               , opDerived = False
               , opParams  = [Typed "foo" "obj"]
               , opPrecond = TLit (LNot  (Atom "f" [AVar "foo"]))
               , opEffects = ELit (LAtom (Atom "f" [AVar "foo"]))
               }
    ]
  }
  -- [ I.Operator { I.opName    = "opA1"
  --              , I.opPre     = []
  --              , I.opEffects = [I.Effect [] ["A"] ["B"]]
  --              }
  -- , I.Operator { I.opName    = "opA2"
  --              , I.opPre     = ["PA"]
  --              , I.opEffects = [I.Effect [] ["A"] []]
  --              }
  -- , I.Operator { I.opName    = "opPA"
  --              , I.opPre     = []
  --              , I.opEffects = [I.Effect [] ["PA"] []]
  --              }
  -- , I.Operator { I.opName    = "opB1"
  --              , I.opPre     = []
  --              , I.opEffects = [I.Effect [] ["B"] ["A"]]
  --              }
  -- , I.Operator { I.opName    = "opB2"
  --              , I.opPre     = ["PB"]
  --              , I.opEffects = [I.Effect [] ["B"] []]
  --              }
  -- , I.Operator { I.opName    = "opPB"
  --              , I.opPre     = []
  --              , I.opEffects = [I.Effect [] ["PB"] []]
  --              }
  -- ]

testProb = Problem { probDomain = "test"
                   , probObjects= [ Typed "A" "obj"
                                  , Typed "B" "obj"
                                  ]
                   , probInit   = []
                   , probGoal   = TAnd [TLit (LAtom (Atom "B" []))]
                   }
-- testProb = I.Problem ["B"] ["B", "A"]


(prob,dom) = compile testProb testDom
test = findPlan prob dom
