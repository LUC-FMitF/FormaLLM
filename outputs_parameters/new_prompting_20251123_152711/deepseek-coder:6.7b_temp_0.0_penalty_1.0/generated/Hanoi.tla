---- MODULE Hanoi -------------------------------
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS D = 3, N = 3 (* D and N can be adjusted *)
VARIABLES towers[0..(2^D)-1]

Init == towers = [i \in 0..((2^D) - 1) |-> IF i < (2^(D-1)) THEN {0} ELSE {} ] /\ Cardinality(\Union{towers[i]: i \in 0..((2^D)-1)}) = D

Next == [t |-> 
    CASE t 
      [] t = EmptyZSeq -> EmptyZSeq
      [] OTHER -> Move(t, NextMove(t))
   ] /\ Cardinality(\Union{towers[i]: i \in 0..((2^D)-1)}) = D
   
Spec == Init /\ [][Next]_<<towers>>

====