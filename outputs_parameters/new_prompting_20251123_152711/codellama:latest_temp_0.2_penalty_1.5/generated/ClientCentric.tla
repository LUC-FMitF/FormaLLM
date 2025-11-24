---- MODULE ClientCentric ----
------------------------------ MODEL STATE SYSTEM ----------------------------
(* The following definitions are based on the paper "Client-Centric Isolation: A New Approach" by Crooks et al. *)
******************************* DEFINITIONS **********************************
CONSTANT Keys == {0, 1} (* set of keys in our system*)
VALUES Values = {"A", "B"}   (* values associated with each key*)
INITIAL_VALUE InitValue <- A(* initial value for all states *)
------------------------------ OPERATIONS ----------------------------
\* An execution e is a sequence of transactions T, where every transaction t in T has its own read state s.t.*  \A i < j: (T[i],s_j) <= (T[j]) *\/   (* total order on the set of all states*)
Execution == [transactions : Seq(Transaction), startTimeStamp, commitTimestamp] /\ (\E transaction IN transactions:\startTimeStamp = MIN{transaction.timestamp}) \/  MAX {transaction.commit} >= COMMIT_TIMESTAMP(* every execution has a unique timestamp *)   (* read states of the system*)
ReadState == [state : State]\* state is complete for T in e iff every operation in t can be executed from s *\/ /\ (\E transaction IN transactions:\A op \in Transaction.operations: ReadStates(op,e))(* write sets *)   (* set of all keys that are written by the system*)
WriteSet == [keys : Set]/\(\forall key\IN Keys,\exists value\IN Values,(key = wKey /\ v=wValue) \/ (~Exists k' IN WriteKeys,k''=\in Key: ~(v==rVal)))(* every write operation has a read state *)
------------------------------ FUNCTIONS ----------------------------  (* functions to calculate the next states for each transaction*)   NextState == [transaction : Transaction] => State /\ (\E op \IN Operations,NextOp = Op.next: (op=wKey/\v==rVal) ==> wValue))(* every write operation has a read state *)
ReadStates(operation IN operations,\execution)\* if the transaction is not in execution return empty set*)   (* function to calculate all possible permutation of transactions given an initialState and list of Transactions*)  Executions == [initialState : State,transactions:Seq] => Set[Execution]\/(\E t \IN T:\A i < j:(t = (T[i],s_j)) ==> s'_J <= s'I) /\ (\forall transaction IN transactions,\exists nextTransaction\in Transaction.next,(transaction=wKey/\v==rVal)\=> wValue)))
(* function to check if a given execution satisfies the commit test*)  CT == [execution : Execution] => Bool \/ (~Exists t1,t2:Ti < Tj:\A op\in Operations:(op = WOp /\ v=wV) ==> ~(v==rVal))
(* function to check if a given execution satisfies the serializability commit test*)  CT_SER == [execution : Execution] => Bool \/ (~Exists t1,t2:Ti < Tj:\A op\in Operations:(op = WOp /\ v=wV) ==> ~(v==rVal))
(* function to check if a given execution satisfies the read committed isolation level*)  CT_RC == [execution : Execution] => Bool \/ (~Exists t1,t2:Ti < Tj:\A op\in Operations:(op = WOp /\ v=wV) ==> ~(v==rVal))
(* function to check if a given execution satisfies the read uncommitted isolation level*)  CT_RU == [execution : Execution] => Bool \/ (~Exists t1,t2:Ti < Tj:\A op\in Operations:(op = WOp /\ v=wV) ==> ~(v==rVal))
(* function to check if a given execution satisfies the snapshot isolation level*)  CT_SSER == [execution : Execution] => Bool \/ (~Exists t1,t2:Ti < Tj:\A op\in Operations:(op = WOp /\ v=wV) ==> ~(v==rVal))
------------------------------ SPECIFICATIONS ----------------------------  (* specification for the system*)   Spec == [initialState : State] => Bool \/ (\E execution IN Executions: CT_SER (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* read committed isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_RC (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* read uncommitted isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_RU (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* snapshot isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_SSER (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
------------------------------ INVARIANTS ----------------------------  (* invariants for the system*)   Invariant == [initialState] => Bool / (\E execution \IN Executions: CT_SER (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* read committed isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_RC (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* read uncommitted isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_RU (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
/\* snapshot isolation level *\/     (/\\ E execution in Execution.nextstate,Txn1 < TXN2 : AOp \IN Operations: CT_SSER (execution)))(* serializability commit test *)    /\(\A transaction\in Transactions:\CT(transaction))
=============================== CONFIGURATION ============================  # Configuration for State System Model Checking with Temporal Logic and TLC.   SPECIFICATION Specification = <<Spec>> ******************************** INVARIANTS Invariants=<<Invariant,CT_SER(execution), CT_RC (transaction) >>*
====