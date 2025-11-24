---- MODULE ClientCentric ----
------------------------- MODEL STATE -------------------------------
CONSTANTS Keys = <<>> : Set  (* set of all keys *)
VALUES    Vals   = << >>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE State =============================
---- MODULEReadWriteSet ----
-------------------------- READWRITESET ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULEReadWriteSet =====================
---- MODELExecution ----
-------------------------- EXECUTION ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODELExecution =====================
-------------------------- TRANSACTIONS ------------------------
CONSTANT Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE Transaction =====================
---- MODELReadWriteSet ----
-------------------------- READWRITESET ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODELReadWriteSet =====================
-------------------------- EXECUTION ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE Execution =====================
---- MODELSerializability ----
-------------------------- SERIALIZABILITY ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE Serializability =====================
---- MODELReadCommitted ----
-------------------------- READCOMMITTED ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE ReadCommitted =====================
---- MODELReadUncommitted ----
-------------------------- READUNCOMMITTED ------------------------
CONSTANTS Keys = << >> : Set  (* set of all keys *)
VALUES    Vals   = <<>>:Set(*set of values*)
INITIALISATION InitState == [k \in Keys |-> v IN Values] * makes it level-1 therefore pass it in*
--------------------------- END -------------------------------
============================= MODULE ReadUncommitted =====================