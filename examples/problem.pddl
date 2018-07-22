
(define (problem Test)

  (:domain Example)

  (:objects
    knight dragon witch - character
    cave castle forest bridge - location)

  (:init
    (at-location knight castle)
    (at-location dragon cave)

    (alive knight)
    (alive dragon)

    (scary dragon)
    (connected cave forest)
    (connected forest bridge)
    (connected bridge castle)
    (frail witch))

  (:goal
    (and (not (and (alive knight) (alive dragon)))
         (at-location knight bridge)
         (at-location dragon bridge)))
)
