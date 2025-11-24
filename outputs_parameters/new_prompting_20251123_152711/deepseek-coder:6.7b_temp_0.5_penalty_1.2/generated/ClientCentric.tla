---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences
TYPE State == [k \in Keys |-> Value] (* A database `State` is represented by keys with corresponding values *)
CONSTANT InitValue /\ PrintT(State) (* TODO InitValue could be bottom (_|_) and we assume that a transaction only writes a key once.*)
TYPE Operation == [op \in {read, write}, k: Key, v : Value]  (* An `Operation` is a read or write of a key and value *)
(* Helpers representing Reads and Writes *)
READS(k) ==  EXTENDS State /\ .~[x \in DOMAIN State |-> (State[x] = InitValue)] == TRUE  (* A helper to check if the state contains read operation for a key k *)
WRITES(k, v) == [op: OpType, x : Key, y : Value ] /\ op = `write` AND x=k AND y=v  ==> EXTENDS State(* A helper to check if the state contains write operation for a key-value pair (k,v)) *)
TYPE Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp] (* A `Transaction` is a total order of `Operation`s *)
OPERATOR " -T-> " /\ OPERATOR "==" 25 (s1 : State) (op : Operation) == \* Definition 1: s −T− > s' ≡ [(k,v)∈s∧(k,v)∉s'] => k∈W_T /\ w(k,v)∈Σ_T=> (k,v)∈s.
TYPE ExecutionElem == [parentState: State, transaction: Transaction, resultState: State] (* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state *) 
OPERATOR " -*-> " /\ OPERATOR "-T=>" 24 (k : Key) (v : Value ) == EXTENDS State(* w(k, v)-to->r(k,v), check reads and writes, implicit because of write check in ReadStates *)
OPERATOR " -*-> " /\ OPERATOR "-T=>" 24 (s1 : State) (transaction: Transaction ) == EXTENDS State(* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s` *)
OPERATOR " -*-> " /\ OPERATOR "-T=>" 24 (k : Key) (v : Value ) == EXTENDS State(* Check types in derived specification, and that it satisfies the isolation level given by commitTest. Definition 5 Given a set of transactions T and their read states *)
OPERATOR " -*-> " /\ OPERATOR "-T=>" 24 (s1 : State) (transaction: Transaction ) == EXTENDS State(* Check types in derived specification, for Snapshot Isolation Strict Serializability Read Committed and Read Uncommitted *)
OPERATOR PrintT(<<>>State) (* print the state to console *)
====