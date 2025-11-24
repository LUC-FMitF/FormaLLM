---- MODULE HDiskSynod ----

(*********************************************************************)
(* Modification History
   Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
   Created Sat Jan 26 15:23:57 CET 2019 by tthai
   /\ (bk.bal = 0) ≡ (bk.inp = NotAnInput) *)
(*********************************************************************)

EXTENDS TLC

CONSTANTS   NotAnInput

VARIABLES   bk == <<>> (* Bank account with no balance and no input *)

NEXT(bk) == IF bk.inp = NotAnInput THEN bk ELSE bk.inp END

SPECIFICATION [](bk.bal = 0)

INVARIANTS
  == \* The bank account balance is always non-negative
     bk.bal >= 0
  END

TLC_CONFIG
  == <<
     (* Specify the algorithm for computing the next-state relation *)
     NextFunction = "NEXT",
     (* Specify the initial state *)
     Init = "<<>>",
     (* Specify the set of labels *)
     Labels = { "bal=0" },
     (* Specify the invariants *)
     Invariants = { "bk.bal >= 0" },
     (* Specify the set of constants *)
     Constants = { "NotAnInput" }
   >>
====