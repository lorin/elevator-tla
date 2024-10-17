---- MODULE elevator ----
EXTENDS Naturals

CONSTANTS N, Up, Dn
ASSUME N \in Nat

VARIABLES i, dir

At(f) == i+1 = 2*f

IsBetween == i % 2 = 0

Init == /\ i = 1
        /\ dir \in {Up, Dn}


UpFlr == /\ \E f \in 1..N-1 : At(f)
         /\ i' = i + 1
         /\ dir' = Up

UpBetween == /\ IsBetween
             /\ dir = Up
             /\ i' = i + 1
             /\ UNCHANGED dir

DnFlr == /\ \E f \in 2..N : At(f)
           /\ i' = i-1
           /\ dir' = Dn

DnBetween == /\ IsBetween
             /\ dir = Dn
             /\ i' = i - 1
             /\ UNCHANGED dir


Next == \/ UpFlr
        \/ UpBetween
        \/ DnFlr
        \/ DnBetween

Spec == Init /\ [][Next]_<<i, dir>>

====