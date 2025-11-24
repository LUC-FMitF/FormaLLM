---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

\* A database `State` is represented by keys with corresponding values
State == [k \in Keys |-> Values]

\* An `Operation` is a read or write of a key and value
Operation == {(k: Key, v: Value) | k \in Keys /\ v \in Values}

\* Helpers representing Reads and Writes
Read == [k \in Keys]
Write == Operation - Read

\* A `Transaction` is a total order of `Operation`s
Transaction == {ops: Seq(Operation), start: TimeStamp, commit: TimeStamp}

\* Represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* The set of all possible permutations of executions given set of transactions
Executions(initialState, transactions) == {
  [e \in Seq(ExecutionElem), e[0].transaction = transactions[0], e[-1].transaction = transactions[-1]] :
    (FORALL i \in 1 ..< Cardinality(transactions)-1 :
      e[i-1].resultState = transactions[i-1] /\ e[i+1].parentState = transactions[i])
}

\* Helper: checks if specific execution satisfies given commit test
CT_SER(transaction, execution) ==
  LET e \in Executions := execution
  IN (FORALL i \in 0 ..< Cardinality(e) : e[i].transaction = transaction /\ e[i].commit <= transaction.commit)

\* Definition 5 Given a set of transactions T and their read states,
a storagesystem satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e).
satisfyIsolationLevel(transactions, CT_SER) == EXISTS execution \in Executions(initialState, transactions): FORALL transaction \in transactions: CT_SER(transaction, execution)

\* Check types in derived specification
CONSTANTS InitValue = {k \in Keys |-> Values} /\ PrintT(State)
====