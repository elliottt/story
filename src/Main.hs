{-# LANGUAGE OverloadedStrings #-}

import Planner
import Planner.Types
import Pretty

main :: IO ()
main  = case findPlan testDomain testAssumps testGoals of
  Just plan -> mapM_ (print . pp) plan
  Nothing   -> putStrLn "No plan"

testDomain =
  [ forall [ "monster", "char", "place" ] $ \ [ monster, char, place ] ->
    Action { aName        = "threaten"
           , aActors      = [ monster ]
           , aHappening   = True
           , aConstraints = [ CPred $ Pred True "monster"   [ monster ]
                            , CPred $ Pred True "character" [ char    ]
                            , CPred $ Pred True "place"     [ place   ]
                            , CNeq monster place
                            ]
           , aPrecond     = [ Pred True "at"    [ monster, place ]
                            , Pred True "at"    [ char,    place ]
                            , Pred True "scary" [ monster        ]
                            ]
           , aEffect      = [ EIntends char (Pred False "alive" [ monster ])
                            ]
           }

  , forall ["char", "monster", "place"] $ \ [ char, monster, place ] ->
    Action { aName        = "slay"
           , aActors      = [ char ]
           , aHappening   = False
           , aConstraints = [ CPred $ Pred True "character" [ char    ]
                            , CPred $ Pred True "monster"   [ monster ]
                            , CPred $ Pred True "place"     [ place   ]
                            , CNeq char monster
                            ]
           , aPrecond     = [ Pred True "at"    [ monster, place ]
                            , Pred True "at"    [ char,    place ]
                            , Pred True "scary" [ monster        ]
                            , Pred True "alive" [ monster        ]
                            , Pred True "alive" [ char           ]
                            ]
           , aEffect      = [ EPred (Pred False "alive" [ monster ])
                            ]
           }

  , forall ["char", "place", "newPlace"] $ \ [char, place, newPlace] ->
    Action { aName        = "go"
           , aActors      = [ char ]
           , aHappening   = True
           , aConstraints = [ CPred $ Pred True "character" [ char     ]
                            , CPred $ Pred True "place"     [ place    ]
                            , CPred $ Pred True "place"     [ newPlace ]
                            , CNeq place newPlace
                            ]
           , aPrecond     = [ Pred True "at"    [ char, place ]
                            , Pred True "alive" [ char        ]
                            ]
           , aEffect      = [ EPred $ Pred False "at" [ char, place ]
                            , EPred $ Pred True  "at" [ char, newPlace ]
                            ]
           }
  ]


testAssumps =
  [ Pred True "place"     [ "Castle" ]
  , Pred True "place"     [ "Forest" ]
  , Pred True "place"     [ "Bridge" ]
  , Pred True "character" [ "Knight" ]
  , Pred True "character" [ "Dragon" ]
  , Pred True "monster"   [ "Dragon" ]
  , Pred True "alive"     [ "Knight" ]
  , Pred True "alive"     [ "Dragon" ]

  , Pred True "at"        [ "Knight", "Forest" ]
  , Pred True "at"        [ "Dragon", "Castle" ]
  , Pred True "scary"     [ "Dragon" ]
  ]

-- XXX swapping the order of these two goals makes it seem like the planner
-- won't terminate
testGoals =
  [ Pred False "alive" [ "Dragon" ]
  , Pred True "at" [ "Dragon", "Bridge" ]
  ]
