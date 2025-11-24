---- MODULE Consensus ----
----------------------------- CONSTANTS ----------------------------
CONSTANT Value = {v1, v2, v3}
INVARIANTS TypeOK Inv
PROPERTY Success
SPECIFICATION LiveSpec
CHECK_DEADLOCK FALSE
=============================== INITIAL STATE ===========================
Init == <<chosen : {}, pc: 0>>.
------------------------------ ACTION Next ----------------------------
Next \/ (<<chosen,pc>> = {v |-> v1} /\ <<pc+1,pc>>) / [pc]
                     == {{chosen := {v2}, pc:=pc + 1}} OR
                      {{chosen := chosen U {v3}, pc:=pc + 1}}.
------------------------------ INVARIANT Inv --------------------------
Inv == <<chosen,pc>> \in Init /\ (<<chosen,pc>> = Success) -> TRUE.
=============================== SPECIFICATION LiveSpec ===================
LiveSpec == [][Next]_vars / [].
****************************** PROPERTY SUCCESS **************************
Success == <<chosen : {v1}, pc: 0 + (pc - 1)>>.
====