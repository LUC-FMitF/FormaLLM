---- MODULE ClientCentric ----

(* Database System *)

CONSTANTS
  Keys = {a, b, c} (* set of keys in the database *)
  Values = {"red", "blue"} (* set of values associated with each key *)
  
VARIABLES
  State: Keys -> Values (* current state of the database *)
  ExecutionElems: Seq(ExecutionElem) (* sequence of execution elements, one for each transaction *)
  
INITIAL STATE
State == [a \in Keys |-> InitValue, b \in Keys |-> InitValue, c \in Keys |-> InitValue]
ExecutionElems == <<>>

TRANSITION OPERATIONS
  Execute(transactions: Seq(Transaction)) ==
    IF transactions = <<>> THEN State ELSE DO
      LET initialState == State (* save current state *)
        executions == [
          e \in ExecutionElems : e.parentState = State,
            e.transaction IN transactions,
            e.resultState = NextState(e.parentState, e.transaction)
        ] (* calculate new execution elements for each transaction in the set of transactions *)
      IF SatisfyIsolationLevel(transactions, initialState) THEN DO
        ExecutionElems == executions + State(* add new state to sequence of execution elements *)
        State == NextState(initialState, transactions) (* update current state with next state for each transaction in the set of transactions *)
      ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF
    ENDDO
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), isolationLevelTest: (Transaction, ExecutionElem) -> Bool) ==
    /\ InitValue \in Values (* check that initial value is in the set of values *)
      /\ PrintT(State) [* print current state *]
        \A execution \in executions(initialState, transactions): isolationLevelTest(execution.transaction, execution) (* for each transaction, apply commit test to corresponding execution element and check that it satisfies the isolation level*)
        
    OBSERVERS
      ExecutionElems == [e |-> NextExecutionElement(e)]
      
FUNCTIONS
  NextState(state: State, transactions: Seq(Transaction)): State (* given current state of database and set of transactions, determine next state *)
    LET updates = {k \in Keys |-> w(k,v) : k \in DOMAIN transactions} (* get all writes in the transaction*)
      updatedState == [k |-> IF k \notin DOMAIN updates THEN State[k] ELSE r(k,v)} (* update state with new values from reads and writes *)
    IN updatedState -*-> state(* check that the read states are not later than the parent state of each transaction*)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transactions |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transaction] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN transactions, e.resultState = readStatesForEmptyTransaction[e.transaction]] (* calculate all possible permutations for each transaction *)
      IF EXISTS e:execution(* check if there exists an execution that satisfies the isolation level*)
        /\ \A t \in Transaction : CT_SER(t, e) THEN TRUE
          ELSE PrintT("Execution not Serializable:", <<transactions>>) ENDIF (* fall back to normal check *)
  
  ReadStatesForEmptyTransaction == [t |-> NextState(initialState, {t})]
    
FUNCTIONS
  Executions(state: State): Seq(ExecutionElem) (* given the current state of database, calculate all possible permutations for each transaction and construct sequence of execution elements *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        ExecutionElems == [e \in ExecutionElems : e.parentState = initialState, e.transaction IN Transactions] (* calculate all possible permutations for each transaction *)
  
  NextExecutionElement(execution: ExecutionElem): ExecutionElem (* given an execution element, determine next execution element for the corresponding transaction *)
    LET newResultState == NextState(execution.parentState, {execution.transaction})(* calculate next state with only one transaction in set of transactions*)
      IF SatisfyIsolationLevel({execution.transaction}, newResultState) THEN DO (* check that the new result state satisfies the isolation level for this execution element *)
        ExecutionElem == [parentState -> State, transaction -> execution.transaction, resultState -> newResultState]
      ELSE PrintT("Execution not Serializable:", <<execution>>) ENDIF
  
  SatisfyIsolationLevel(transactions: Seq(Transaction), state: State): Bool (* given a set of transactions and current state of database, check that all execution elements for these transactions satisfy the isolation level *)
    LET initialState == state (* save current state*)
      readStatesForEmptyTransaction = {t \in Transaction |-> NextState(initialState, {t})} (* get new states with only one transaction in set of transactions*)
        executions == [e \in ExecutionEle
====