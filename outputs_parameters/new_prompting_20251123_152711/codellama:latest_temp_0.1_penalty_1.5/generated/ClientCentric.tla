---- MODULE ClientCentric ----
------------------------------ MODEL STATE ----------------------------
CONSTANTS Keys = <<k1, k2>> : SET OF STRING; (* set of all keys *)
Values  == {v}   ;                           (* value domain for each key*)
InitValue    \* initial values *\            (INITIAL_VALUE) InitValue := v.(* default inital state is a single element with the given value.*);
State        = [k |-> Set(<<>>)] : SET OF STRING -> VALUES; (* set of all states *)
ExecutionElem == {parentState: State, transaction: Transaction} ;  (\* an execution elem represents one step in our state machine *\)                             (INITIAL_VALUE) Execution = << >>.(* initial empty list*)
\------------------------------ MODEL STATE ----------------------------/;
============================= MODULE State =====================
---- MODULEReadStates ----
******************************* READSTATES ******************
LOCAL INSTANCE FiniteSets ; (* finite sets are used to represent read states *)
\** Read States ** \                            (INITIAL_VALUE)  ExecutionElem.readState = << >>;(* initial empty list*)Execution == [ops: Seq(Operation), start: TimeStamp, commit: Timestamp] : SET OF EXECUTION ELEM ; (* a transaction is represented by its sequence of operations and the time it was started *)
\** Read States ** \                            (INITIAL_VALUE)  ExecutionElem.readState = << >>;(* initial empty list*)Execution == [ops: Seq(Operation), start: TimeStamp, commit: Timestamp] : SET OF EXECUTION ELEM ; (* a transaction is represented by its sequence of operations and the time it was started *)
\------------------------------ MODULEReadState ----------------------------/;
============================= MODEL Read States =====================