---- MODULE MCelevator ----
EXTENDS elevator

Alias == [
    i |-> i,
    floor |-> IF IsBetween THEN "between" ELSE (i+1) \div 2,
    dir |-> dir
]


Range == /\ i \geq 0
         /\ i \leq 2*N-1


GetsStuckBetweenFloors == <>[]IsBetween
DoesntGetsStuckBetweenFloors == ~GetsStuckBetweenFloors

VisitsEveryFloor == [] \A f \in 1..N : <>At(f)


====