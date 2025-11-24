---- MODULE ClientCentric -------------------------------
EXTENDS <standard modules>
CONSTANTS Keys, InitValue, Values
VARIABLES State, Execution <<ExecutionElem>>, Transaction, Operation, TimeStamp, Seq(Operation), Reads, Writes

Init == State = [k \in Keys |-> InitValue] /\ Execution = {}
Next == ... (* Define your next state relation here *)
Spec == Init /\ [][Next]_<<State>>

====