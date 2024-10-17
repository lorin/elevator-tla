---- MODULE elevator ----
EXTENDS Naturals

CONSTANTS N, \* number of floors
          Up, Dn  \* represents direction
ASSUME N \in Nat

VARIABLES i, dir

(* True when elevator is at floor f *)
At(f) == i = 2 * f - 1

(* True when elevator is between floors *)
IsBetween == i % 2 = 0

Init == /\ i = 1
        /\ dir \in {Up, Dn}

(* move up when at a floor *)
UpFlr == /\ \E f \in 1..N-1 : At(f)
         /\ i' = i + 1
         /\ dir' = Up

(* move up when between floors *)
UpBetween == /\ IsBetween
             /\ dir = Up
             /\ i' = i + 1
             /\ UNCHANGED dir

(* move down when at a floor *)
DnFlr == /\ \E f \in 2..N : At(f)
         /\ i' = i-1
         /\ dir' = Dn

(* move down when between floors *)
DnBetween == /\ IsBetween
             /\ dir = Dn
             /\ i' = i - 1
             /\ UNCHANGED dir

Next == \/ UpFlr
        \/ UpBetween
        \/ DnFlr
        \/ DnBetween

v == <<i, dir>>

L == /\ WF_v(UpBetween)
     /\ WF_v(DnBetween)
     /\ WF_v(UpFlr /\ At(1))
     /\ WF_v(DnFlr /\ At(N))
     /\ \A f \in 2..N-1 :
        /\ SF_v(UpFlr /\ At(f))
        /\ SF_v(DnFlr /\ At(f))

Spec == Init /\ [][Next]_v /\ L

====