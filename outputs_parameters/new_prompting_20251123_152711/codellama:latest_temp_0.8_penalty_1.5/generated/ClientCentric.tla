---- MODULE ClientCentric ----
----------------------------------------- MODEL --------------------------------
(* This module provides a model of client centric isolation. It is based on the definitions given in Tim Soethout et al, Automated Validation of State-Based *)
(*Client-Centred Isolation with TLA+: https://doi.org/10.1007%2F978-3-030-67220-1_4*)
\* The model consists of a set of operations, which can be either reads or writes to keys in the database *)
(* A transaction is an ordered sequence (or permutation) of these operation. We assume that transactions are atomic and cannot overlap.*\)
\*\[Op(op)] == Op = {read | write} \* An execution represents a particular instance where multiple operations were executed as part of some transaciton*)
(* The state is the current value for each key in our database *)
State ::= [Keys -> Values]   /\ InitValue \in Values  *//** A transaction has two components: its read and write sets. For simplicity, we assume that a single operation only writes to one location at most*\) Tx == {read : Set(Key), writtenVal} /\\ \{writtenLoc |-> Loc}\/* An execution is an ordered sequence of transactions*/
Execution ::= [Txs -> Transaction] /\ ExecutionElem = [[parentState: State, transaction: Transactions]] *//** A set of keys that a single operation can read from the database. For simplicity we assume there exists no conflict between different operations*\) ReadStatesForOp == Set(Key) /\\ \{k |-> v}  \*\[ReadSet]
\/\ [Rs -> RS]\/* The parent state is the last seen key value pair in our execution before applying a transaction. Note that this does not necessarily correspond to an actual previous states, but rather *//** A set of keys for which we know there exists at least one read operation*/ ReadStatesForEmptyTransaction == Set(Key) /\\ \{k |-> v}  \*\[ReadSet]
\/\ [Rs -> RS]\/* The write set is the union over all operations in a transaction. For simplicity, assume that each location written to by an op only occurs once*\) WrittenLocationsForOp == Set(Key) /\\ \{k |-> v}  \*\[WrittenSet]
\/\ [WS -> WS]\/* A set of keys for which we know there exists at least one write operation. For simplicity, assume that each location written to by an op only occurs once*\) WrittenLocationsForEmptyTransaction == Set(Key) /\\ \{k |-> v}  \*\[WrittenSet]
\/\ [WS -> WS]\/* A set of transactions ordered in the way they were executed. Each transaction is composed from a sequence (permutation!) of operations*\) Transactions ::= [[Tx]] /\ ExecutionElem = [\[\parentState: State, TXs : Set(Trans)]] *//** The parent state for an execution consists only of key value pairs where the write set does not intersect with any previous states*/
ParentStatesForExecution == [EXEC -> PARENT_STATE]\/\[PSTS->PSRVT]/[\parentState: State, TXs : Set(Trans)]
====