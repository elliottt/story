
(define (domain Example)

  (:types
    character location magnitude - object
  )

  (:constants
    none minor major vast - magnitude
  )

  (:properties
    (scary ?x - character)
    (connected ?from ?to - location)
  )

  (:predicates
    (alive ?who - character)
    (injured ?who - character)
    (conscious ?who - character)
    (at-location ?who - character ?where - location)
    (scared ?who - character)
  )

  (:action travel
    :parameters (?actor - character ?from ?to - location)
    :precondition
      (and (at-location ?actor ?from)
           (not (or (= ?from ?to) (injured ?actor)))
           (alive ?actor)
           (consciousk?actor)
           (or (connected ?from ?to) (connected ?to ?from)))
    :effect
      (and (at-location ?who ?to)
           (not (at-location ?who ?from))))

  (:action intimidate
    :parameters
      (?actor ?target - character ?loc - location)

    :precondition
      (and (at-location ?actor ?loc)
           (at-location ?target ?loc)
           (not (= ?actor ?target))
           (alive ?actor)
           (alive ?target)
           (scary ?actor))

    :effect
      (scared ?target))
)
