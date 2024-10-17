---- MODULE MCelevator ----
EXTENDS elevator


Range == /\ i \geq 0
         /\ i \leq 2*N-1


GetsStuck == <>[]IsBetween

DoesntGetsStuck == ~GetsStuck

VisitsEveryFloor == [] \A f \in 1..N : <>At(f)

====