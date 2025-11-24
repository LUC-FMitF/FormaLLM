---- MODULE MultiPaxos_MC ----

(***********************************************************************************************)
(* TLC config-related defs.                                                                   *)
(***********************************************************************************************)
CONSTANTS    ConstMaxBallot \* Maximum ballot value, should be replaced by actual maximum      *)
                            \* in your system                                                   *)
VARIABLES    Ballots        \* The set of all current ballots                                  *)
-----------------------------------------------------------------------------------------------
Init == ...                  \* Initial state predicate                                      *)
Next == ...                  \* Next-state relation                                          *)
Spec == Init /\ [][Next]_<<...>>  \* Specification                                            *)
---------------------------------------- MODULE ReplicatedStateMachine END --------------------------------------------------
(***********************************************************************************************)
(* Type check invariant.                                                                       *)
(***********************************************************************************************)
TypeOK ==  ...                \* Placeholder for type checking, should be defined              *)
------------------------------- INVARIANTS SECTION END ----------------------------------------
===============================================================================================
====
SPECIFICATION Spec /\ TypeOK /\ Linearizability
(***********************************************************************************************)
(* Symmetry related defs.                                                                      *)
(***********************************************************************************************)
SYMMETRY    SymmetricPerms  \* Placeholder for symmetry checking, should be defined           *)
------------------------------- SYMMETRY SECTION END ----------------------------------------
===============================================================================================
====
CHECK_DEADLOCK TRUE            \* Check deadlock                                            *)
====