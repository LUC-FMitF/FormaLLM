---- MODULE ClientCentric ----

(* A database `State` is represented by keys with corresponding values *)
\* An operation is a read or write of a key and value *\/
DATATYPE Operation = Read(key: Key, valInDB: Value) | Write(key:Key,valToWrite :Value) \/ /\ InitValu /in Values /\ PrintT (State).
\* A transaction is a total order of operations. It consists of an ordered sequence *\/
DATATYPE Transaction = [ops:\Seq Operation] /\ /\ ops not empty .
(* The parent state is the last state in the execution, but it's not used for isolation *)
CONSTANT ResultState == State \/ PrintT(ResultState) /.
\* An `Execution` represents a sequence of transactions with their corresponding *\/
DATATYPE Execution = [parentStates:\Seq (Transaction => ParentState), transaction: Transaction, resultState :ParentState] /\ (* We store the start and commit time in lookup functions *)  \/ parentStates not empty .  
\* Read states are from which state can an operation read its value *\/
CONSTANT READ_STATES = [s:\Seq (Transaction => ParentState) | s.transaction -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT COMPLETE_FOR = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* The write sets are the keys that a transaction updates: WT= {k|w(k,v)\in Values} *\/
CONSTANT WriteSet = [s:\Seq (Transaction => ParentState) | w(k, v):Values /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* The write sets are the keys that a transaction updates: WT= {k|w(k,v)\in Values} *\/
CONSTANT WriteSet = [s:\Seq (Transaction => ParentState) | w(k, v):Values /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.  \/ parentStates not empty .  
\* A state `state` is complete for a set of transactions in an execution if every operation *\/
CONSTANT NO_COMMIT = [s:\Seq (Transaction => ParentState) | s -o-> ResultState /\ PrintT(ParentState)] /.
====