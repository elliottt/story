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
                            , CNeq monster char
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
           , aHappening   = False
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
  [ EPred $ Pred True "place"     [ "Castle" ]
  , EPred $ Pred True "place"     [ "Forest" ]
  , EPred $ Pred True "place"     [ "Bridge" ]
  , EPred $ Pred True "character" [ "Knight" ]
  , EPred $ Pred True "character" [ "Dragon" ]
  , EPred $ Pred True "character" [ "Grue" ]
  , EPred $ Pred True "monster"   [ "Dragon" ]
  , EPred $ Pred True "monster"   [ "Grue" ]
  , EPred $ Pred True "alive"     [ "Knight" ]
  , EPred $ Pred True "alive"     [ "Dragon" ]
  , EPred $ Pred True "alive"     [ "Grue" ]

  , EPred $ Pred True "at"        [ "Knight", "Castle" ]
  , EPred $ Pred True "at"        [ "Dragon", "Forest" ]
  , EPred $ Pred True "at"        [ "Grue", "Bridge" ]
  , EPred $ Pred True "scary"     [ "Dragon" ]
  , EPred $ Pred True "scary"     [ "Grue" ]

    -- required, as going somewhere requires character intent
  , EIntends "Dragon" (Pred True "at" ["Dragon", "Bridge"])
  , EIntends "Knight" (Pred True "at" ["Knight", "Bridge"])
  ]

testGoals =
  [ Pred False "alive" [ "Dragon" ]
  , Pred True "at" [ "Dragon", "Bridge" ]
  , Pred False "alive" [ "Grue" ]
  ]
