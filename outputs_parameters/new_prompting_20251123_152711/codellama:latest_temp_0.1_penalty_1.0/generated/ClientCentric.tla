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

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction` is a total order of `Operation`s
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A `State` is a function from keys to values
State == [key: Keys |-> value: Values]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `ExecutionElem` is an element of an `Execution`
ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]

\* A `Execution` is a sequence of `Transaction`s with their corresponding parent state.
Execution == [parentState: State, transaction: Transaction, resultState: State]

\* A `Transaction
====