
(define (domain Example)

  (:types
    character location - object
  )

  (:predicates
    (scary ?x - character)
    (connected ?from ?to - location)
    (frail ?x - character)
    (alive ?who - character)
    (injured ?who - character)
    (at-location ?who - character ?where - location)
    (scared ?who - character)
  )

  (:action travel-forwards
    :parameters (?actor - character ?from ?to - location)
    :precondition
      (and (at-location ?actor ?from)
           (not (= ?from ?to))
           (not (injured ?actor))
           (alive ?actor)
           (connected ?from ?to))
    :effect
      (and (at-location ?actor ?to)
           (not (at-location ?actor ?from))))

  (:action travel-backwards
    :parameters (?actor - character ?from ?to - location)
    :precondition
      (and (at-location ?actor ?to)
           (not (= ?from ?to))
           (not (injured ?actor))
           (alive ?actor)
           (connected ?to ?from))
    :effect
      (and (at-location ?actor ?from)
           (not (at-location ?actor ?to))))

  (:action intimidate
    :parameters
      (?actor ?target - character ?loc - location)

    :precondition
      (and (at-location ?actor ?loc)
           (at-location ?target ?loc)
           (not (= ?actor ?target))
           (not (scared ?target))
           (alive ?actor)
           (alive ?target)
           (scary ?actor))

    :effect
      (and (scared ?target)))
)
