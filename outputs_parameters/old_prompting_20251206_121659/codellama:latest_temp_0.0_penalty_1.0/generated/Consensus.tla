---- MODULE Consensus ----
EXTENDS Naturals
CONSTANTS
  Value = {v1, v2, v3}
VARIABLES
  chosen = {}
  pc = 0

Init ==
  chosen = {} /\ pc = 0

Next ==
  pc' = pc + 1
  IF pc = 0
  THEN
    chosen' = {}
  ELSE
    WITH (v \in Value)
    chosen' = {v}

Spec ==
  Init /\ [][Next]_<<chosen, pc>>

Inv ==
  TypeOK /\
  chosen' = {} \/ chosen' = {v} /\ v \in Value

Success ==
  chosen' = {v} /\ v \in Value

LiveSpec ==
  Init /\ [][Next]_<<chosen, pc>> /\
  SUCCESS

TypeOK ==
  TRUE

Inv ==
  TRUE

Success ==
  TRUE

=============================================================================
====