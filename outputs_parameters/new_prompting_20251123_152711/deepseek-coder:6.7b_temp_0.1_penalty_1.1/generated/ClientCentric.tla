---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Keys = {...}  (* Replace this with the set of keys *)
CONSTANTS InitValue = ... (* Replace this with the initial value for each key *)
CONSTANTS Values = {...}  (* Replace this with the set of possible values *)

\* An operation is a read or write of a key and value
Operation == [op: {"read", "write"}, key: Keys, value: Values]

\* A transaction is a total order of operations
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* The state of the database after applying a transaction to it
NextState(s, t) == ... (* Replace this with your next state calculation *)

\* A sequence of transactions with their corresponding parent state
Execution == Seq(ExecutionElem)

\* Check if a specific execution satisfies a given commit test
CT_SER(transaction, execution) == 
  EXISTS i \in 1..Len(execution) /\ execution[i].transaction = transaction :
    execution[i-1].resultState -T-> execution[i].parentState

\* Check if the database satisfies a given isolation level
satisfyIsolationLevel(transactions, CT_SER) == 
  EXISTS execution \in Executions(initialState, transactions): 
    ALL transaction \in transactions : CT_SER(transaction, execution)

\* The set of all possible permutations of executions given a set of transactions
Executions(initialState, transactions) == Permutations(Seq2Set(transactions))

\* Helper function to generate all possible permutations of a sequence
Permutations(s) == 
  IF s = {} THEN {{} \in Powerset(Powerset(Domain(s)))}
  ELSE UNION {{x} | x \in Domain(s)} O ({y, Rest} \in Permutations(Rest) /\ y \notin Domain(s))

\* Helper function to convert a sequence to a set
Seq2Set(seq) == IF seq = {} THEN {} ELSE {x | x \in Domain(seq)}

\* Check if the database satisfies strict serializability (SSI)
CT_SSER(timestamps) == 
  EXISTS t1,t2 \in timestamps : 
    t1 < t2 /\ FORALL s \in State : 
      (s.timestamp = t1 ==> EXISTS t3 \in timestamps : t3 > t1 /\ t3 <= t2)

\* Check if the database satisfies read committed (RC)
CT_RC(timestamps) == 
  EXISTS t1,t2 \in timestamps : 
    t1 < t2 /\ FORALL s \in State : 
      (s.timestamp = t1 ==> EXISTS ops \in Transaction[ops] : ops.key NOTIN Domain(s) OR ops.value = s[ops.key])

\* Check if the database satisfies read uncommitted (RU)
CT_RU(timestamps) == 
  EXISTS t1,t2 \in timestamps : 
    t1 < t2 /\ FORALL s \in State : 
      (s.timestamp = t1 ==> EXISTS ops \in Transaction[ops] : ops.key NOTIN Domain(s) OR ops.value = s[ops<｜begin▁of▁sentence｜>.timestamp])
====