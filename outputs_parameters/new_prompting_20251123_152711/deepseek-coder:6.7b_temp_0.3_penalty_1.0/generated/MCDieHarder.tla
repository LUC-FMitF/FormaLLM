---- MODULE MCDieHarder ----


EXTENDS Module DieHarder

CONSTANTS Goal     = <4>

VARIABLES Jug      <- MCJug
         Capacity <- MCCapacity

SPECIFICATION Spec

INVARIANTS TypeOK NotSolved

=============================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES NotFull, Full

Init ==
  /\ NotFull = {1..Capacity}
  /\ Full = {}
  /\ UNCHANGED {Goal}

Next ==
  /\ MCJug' = IF Jug \in Full THEN Jug \ {Choose x : x \in Full}
              ELSE Jug \ {Choose x : x \in NotFull}
  /\ MCCapacity' = IF Jug \in Full THEN Jug \ {Choose x : x \in Full}
              ELSE Jug \ {Choose x : x \in NotFull}
  /\ NotFull' = IF Jug \in Full THEN NotFull \ {Choose x : x \in Full}
              ELSE NotFull \ {Choose x : x \in NotFull}
  /\ Full' = IF Jug \in Full THEN Full \ {Choose x : x \in Full}
              ELSE Full \ {Choose x : x \in NotFull}
  /\ UNCHANGED {Goal}

Spec == Init /\ [](NotFull \in Full)

INVARIANTS TypeOK NotSolved

=============================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES NotFull, Full

Init ==
  /\ NotFull = {1..Capacity}
  /\ Full = {}
  /\ UNCHANGED {Goal}

Next ==
  /\ MCJug' = IF Jug \in Full THEN Jug \ {Choose x : x \in Full}
              ELSE Jug \ {Choose x : x \in NotFull}
  /\ MCCapacity' = IF Jug \in Full THEN Jug \ {Choose x : x \in Full}
              ELSE Jug \ {Choose x : x \in NotFull}
  /\ NotFull' = IF Jug \in Full THEN NotFull \ {Choose x : x \in Full}
              ELSE NotFull \ {Choose x : x \in NotFull}
  /\ Full' = IF Jug \in Full THEN Full \ {Choose x : x \in Full}
              ELSE Full \ {Choose x : x \in NotFull}
  /\ UNCHANGED {Goal}

Spec == Init /\ [](NotFull \in Full)

INVARIANTS TypeOK NotSolved

=============================================================
====

TLC Configuration:

CONSTANTS Goal     = <4>
          Jug      <- MCJug
          Capacity <- MCCapacity

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====