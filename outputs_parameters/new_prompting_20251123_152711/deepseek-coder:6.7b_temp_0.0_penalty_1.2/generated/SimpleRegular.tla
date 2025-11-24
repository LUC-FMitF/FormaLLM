---- MODULE SimpleRegular ----
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS N
VARIABLES x[0..(N-1)], y[0..(N-1)]

Init == <x> = [i \in 0..(N-1) |-> {0}], <y> = [i \in 0..(N-1) |-> {0}]
Next == proc == 0..(N-1) -> <x[proc]> = IF self = 0 THEN {{0},{1}} ELSE {{1}} /\ <y[proc]> = <x[(self-1) % N]>
Spec == Init /\ [][][Next]_<x, y> ~~ <x, y>

====