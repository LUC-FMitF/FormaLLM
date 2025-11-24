---- MODULE ClientCentric -------------------------------------------------------
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS InitValue = _|_ /\ PrintT(State)
----------------------------------------------- INVARIANTS and CONFIGURATION -----
INVARIANT LengthInvariant == \A s: State -> ZLen(s.seq) <= Cardinality(DomSeq) * MaxLength  (* ensures sequence length doesn't exceed maximum *)
CONSTANTS MaxLength = 100 /\ CheckTypes = TRUE /\ Keys, Values : SetOf ... /\ DomSeq = { s: State |-> ZLen(s.seq)} - (EmptyZSeq) (* Define other constants here *)
----------------------------------------------- DEFINITION OF TRANSACTION --------
Transaction == [ops : Sequence of Operation, start/commit : TimeStamp] /\ CheckTypesOfTuple((Sequence of Operation),(TimeStamp), (TimeStamp))(* Add more fields to Transaction as needed *)
----------------------------------------------- DEFINITION OF EXECUTION ELEMENT ----- 
ExecutionElem == [parentState: State, transaction : Transaction , resultState : State] /\ CheckTypesOfTuple((State),(Transaction), (State)) (* Add other invariants/checks as needed *)
----------------------------------------------- DEFINITION OF FUNCTIONS and OPERATORS ----- 
...(* Define functions for operations on Sequence, Set etc. as required by your system here*)
====