---- MODULE MCelevator ----
EXTENDS elevator


Range == /\ i \geq 0
         /\ i \leq 2*N-1


Stuck == []IsBetween

NeverStuck == ~<>Stuck

====