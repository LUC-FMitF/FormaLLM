---- MODULE ClientCentric ----

CONSTANTS Keys = <<k1, k2>>
INITIAL_VALUE InitialValue == 0
\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
COMPUTE ReadStatesForEmptyTransaction(transactions) \/ (IF transactions = <<>> THEN Keys ELSE {}) END IF
FUNCTION ExecutionElem == [parentState: State, transaction: Transaction]
\* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
COMPUTE Executions(initialState) \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]
\* A transaction is a total order of `Operation`s.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Operation == [opType: OpType, key: Key, value: Value]
\* An operation is a read or write of a `Key` and `Value`.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION OpType == [read, write]
\* We distinguish between two types of operations: read and write.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Key == k1 OR k2
\* A `Key` is a key in the system's state that can be read or written.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Value == [v1, v2] OR {v3}
\* A `Value` is a value in the system's state that can be read or written.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION TimeStamp == [t1, t2] OR {t3}
\* A `TimeStamp` is a timestamp in the system's state that can be read or written.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION State == [k1: Value, k2: Value] OR {v3}
\* A `State` is a set of key-value pairs in the system's state.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION InitValue == [v1, v2] OR {v3}
\* The `InitValue` is the value that a key-value pair in an empty state has.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION ReadStatesForEmptyTransaction(transactions: Seq(Transaction)) == {s1, s2} OR {}
\* The `ReadStatesForEmptyTransaction` is the set of read states for an empty transaction. For simplicity we store all previous states in a lookup function and assume that every operation can only be applied to these states.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transactions(initialState: State, transactions: Seq(Transaction)) == [t1, t2] OR {}
\* The `Transactions` is a set of all possible permutations of the given transaction. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transaction(ops: Seq(Operation), start: TimeStamp, commit: TimeStamp) == [t1, t2] OR {}
\* The `Transaction` is a total order of operations. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Operation(opType: OpType, key: Key, value: Value) == [t1, t2] OR {}
\* The `Operation` is a read or write of a key and value. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION OpType(read, write) == [t1, t2] OR {}
\* The `OpType` is a type of operation that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Key(k1, k2) == [t1, t2] OR {}
\* The `Key` is a key in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Value(v1, v2) == [t1, t2] OR {}
\* The `Value` is a value in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION TimeStamp(t1, t2) == [t1, t2] OR {}
\* The `TimeStamp` is a timestamp in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION State(k1: Value, k2: Value) == [t1, t2] OR {}
\* The `State` is a set of key-value pairs in the system's state. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION InitValue(v1, v2) == [t1, t2] OR {}
\* The `InitValue` is the value that a key-value pair in an empty state has. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION ReadStatesForEmptyTransaction(transactions: Seq(Transaction)) == {s1, s2} OR {}
\* The `ReadStatesForEmptyTransaction` is the set of read states for an empty transaction. For simplicity we store all previous states in a lookup function and assume that every operation can only be applied to these states.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transactions(initialState: State, transactions: Seq(Transaction)) == [t1, t2] OR {}
\* The `Transactions` is a set of all possible permutations of the given transaction. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transaction(ops: Seq(Operation), start: TimeStamp, commit: TimeStamp) == [t1, t2] OR {}
\* The `Transaction` is a total order of operations. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Operation(opType: OpType, key: Key, value: Value) == [t1, t2] OR {}
\* The `Operation` is a read or write of a key and value. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION OpType(read, write) == [t1, t2] OR {}
\* The `OpType` is a type of operation that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Key(k1, k2) == [t1, t2] OR {}
\* The `Key` is a key in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Value(v1, v2) == [t1, t2] OR {}
\* The `Value` is a value in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION TimeStamp(t1, t2) == [t1, t2] OR {}
\* The `TimeStamp` is a timestamp in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION State(k1: Value, k2: Value) == [t1, t2] OR {}
\* The `State` is a set of key-value pairs in the system's state. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION InitValue(v1, v2) == [t1, t2] OR {}
\* The `InitValue` is the value that a key-value pair in an empty state has. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION ReadStatesForEmptyTransaction(transactions: Seq(Transaction)) == {s1, s2} OR {}
\* The `ReadStatesForEmptyTransaction` is the set of read states for an empty transaction. For simplicity we store all previous states in a lookup function and assume that every operation can only be applied to these states.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transactions(initialState: State, transactions: Seq(Transaction)) == [t1, t2] OR {}
\* The `Transactions` is a set of all possible permutations of the given transaction. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transaction(ops: Seq(Operation), start: TimeStamp, commit: TimeStamp) == [t1, t2] OR {}
\* The `Transaction` is a total order of operations. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Operation(opType: OpType, key: Key, value: Value) == [t1, t2] OR {}
\* The `Operation` is a read or write of a key and value. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION OpType(read, write) == [t1, t2] OR {}
\* The `OpType` is a type of operation that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Key(k1, k2) == [t1, t2] OR {}
\* The `Key` is a key in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Value(v1, v2) == [t1, t2] OR {}
\* The `Value` is a value in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION TimeStamp(t1, t2) == [t1, t2] OR {}
\* The `TimeStamp` is a timestamp in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION State(k1: Value, k2: Value) == [t1, t2] OR {}
\* The `State` is a set of key-value pairs in the system's state. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION InitValue(v1, v2) == [t1, t2] OR {}
\* The `InitValue` is the value that a key-value pair in an empty state has. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION ReadStatesForEmptyTransaction(transactions: Seq(Transaction)) == {s1, s2} OR {}
\* The `ReadStatesForEmptyTransaction` is the set of read states for an empty transaction. For simplicity we store all previous states in a lookup function and assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transactions(initialState: State, transactions: Seq(Transaction)) == [t1, t2] OR {}
\* The `Transactions` is a set of all possible permutations of the given transaction. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Transaction(ops: Seq(Operation), start: TimeStamp, commit: TimeStamp) == [t1, t2] OR {}
\* The `Transaction` is a total order of operations. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Operation(opType: OpType, key: Key, value: Value) == [t1, t2] OR {}
\* The `Operation` is a read or write of a key and value. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION OpType(read, write) == [t1, t2] OR {}
\* The `OpType` is a type of operation that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Key(k1, k2) == [t1, t2] OR {}
\* The `Key` is a key in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION Value(v1, v2) == [t1, t2] OR {}
\* The `Value` is a value in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
FUNCTION TimeStamp(t1, t2) == [t1, t2] OR {}
\* The `TimeStamp` is a timestamp in the system's state that can be read or written. For simplicity we assume that every operation can only be applied to these states and store them in an array for easy access.
COMPUTE ExecutionElem \/ (IF initialState = <<>> THEN [] ELSE [[[InitialValue |-> 0]]] END IF) END IF
====