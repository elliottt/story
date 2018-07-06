
(define (problem Test)

  (:domain Example)

  (:objects
    knight dragon - character
    cave castle forest bridge - location)

  (:init
    (at-location knight castle)
    (at-location dragon cave)

    (alive knight)
    (alive dragon)

    (scary dragon)
    (connected cave forest)
    (connected forest bridge)
    (connected bridge castle))

  (:goal
    (and (not (and (alive knight) (alive dragon)))
         (at-location knight bridge)
         (at-location dragon bridge)))
)
