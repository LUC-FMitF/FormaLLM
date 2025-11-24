---- MODULE ClientCentric ----

(***************************************************************************)
(* A database `State` is represented by keys with corresponding values *)
(***************************************************************************)

CONSTANT Keys
CONSTANT Values
CONSTANT InitValue

\* An `Operation` is a read or write of a key and value
Operation == [key: Keys, value: Values]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction is serializable
CommitTest == [transaction: Transaction, execution: Execution]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [elems: Seq(ExecutionElem)]

\* A `ExecutionElem` is a single element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `ExecutionElem`s
Execution == [elems: Seq(ExecutionElem)]

\* A `Transaction` is a sequence of `Operation`s
Transaction == [ops: Seq(Operation)]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `TimeStamp` is a natural number
TimeStamp == Nat

\* A `Seq` is a sequence of elements
Seq == [elem: Elem*]

\* A `Elem` is a single element of a `Seq`
Elem == [key: Keys, value: Values]

\* A `Set` is a set of elements
Set == [elem: Elem*]

\* A `Keys` is a set of keys
Keys == [key: Keys*]

\* A `Values` is a set of values
Values == [value: Values*]

\* A `InitValue` is a value that is used as the initial value for a key
InitValue == [value: Values]

\* A `PrintT` is a function that prints a transaction
PrintT == [transaction: Transaction]

\* A `SerializabilityDebug` is a function that checks if a transaction is serializable
SerializabilityDebug == [initialState: State, transactions: Seq(Transaction)]

\* A `SnapshotIsolation` is a function that checks if a transaction is serializable
SnapshotIsolation == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadCommitted` is a function that checks if a transaction is serializable
ReadCommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `ReadUncommitted` is a function that checks if a transaction is serializable
ReadUncommitted == [initialState: State, transactions: Seq(Transaction)]

\* A `IsolationLevel` is a function that checks if a transaction is serializable
IsolationLevel == [initialState: State, transactions: Seq(Transaction)]

\* A `CommitTest` is a function that checks if a transaction
====