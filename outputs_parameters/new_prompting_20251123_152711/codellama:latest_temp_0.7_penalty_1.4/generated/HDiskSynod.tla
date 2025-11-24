---- MODULE HDiskSynod ----

(****************************************************************************)
(* Modification History                                                      *)
(****************************************************************************)
(** Last modified Sat Jan 26 15:52:41 CET 2019 by tthai **)
(** Created Sat Jan 26 15:23:57 CET 2019 by tthai **)
(****************************************************************************)
CONSTANTS Bank, Input, NotAnInput \* Define all symbols before use           *)
LOCAL INSTANCE FiniteSets          (* Include TLC config after ====            *)
CONFIGURE SPECIFICATION Spec        (\*) The specification of the module       *)
INVARIANTS Inv                    (\*) The invariants of the module         *)
CONSTANT B, I \* Instantiate Bank and Input constants from outside world   *)
=============================================================================
====