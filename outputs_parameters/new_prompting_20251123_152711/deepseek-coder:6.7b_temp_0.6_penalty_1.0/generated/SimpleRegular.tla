---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module is a minor modification of the algorithm in module Simple.   *)
(* It considers only registers that can be written by a single process, but *)
(* takes into account that reads and writes are not instantaneous atomic    *)
(* actions, but take a finite length of time and can overlap.  An atomic   *)
(* register is one in which a read and write acts as if it were executed    *)
(* atomically at some time between the beginning and end of the operation.  *)
(* A regular register is defined in the paper "On Interprocess Communication *)
(* Distributed Computing 1, 2 (1986), 77-101" which can be found on the Web *)
(* at http://lamport.azurewebsites.net/pubs/interprocess.pdf.  That paper   *)
(* considers only registers that can be written by a single process, but    *)
(* takes into account that reads and writes are not instantaneous atomic    *)
(* actions, but take a finite length of time and can overlap.  An atomic   *)<｜begin▁of▁sentence｜>
(* register is one in which a read and write acts as if it were executed    *)
(* atomically at some time between the beginning and end of the operation.  *)
(* A regular register is defined in the paper "On Interprocess Communication *)
(* Distributed Computing 1, 2 (1986), 77-101" which can be found on the Web *)
(* at http://lamport.azurewebsites.net/pubs<｜begin▁of▁sentence｜>
(***************************************************************************)

EXTENDS FiniteSets, Naturals, ZSequences

CONSTANT N = 8

VARIABLES
  x = [i \in 0..(N-1) |-> {0}],
  y = [i \in 0..(N-1) |-> {0}]

PROCESSES
  proc == [i \in 0..(N-1)]

(* process actions *)
  a1 == x[self] := {0,1}
  a2 == x[self] := {1}
  b  == with (v \in x[(self-1) % N]) [y[self] := v]

(* specification *)
SPECIFICATION
  Init == (x[i] = {0} FORALL i \in 0..(N-1)) /\ (y[i] = {0} FORALL i \in 0..(N-1))
  Trans == (x[self] IN {0,1} FORALL self) /\ (y[self] = x[self] FORALL self)

(* invariants *)
INVARIANTS
  PCorrect == 
    (x[i] SUBSET {0,1} FORALL i \in 0..(N-1)) /\ 
    (y[i] = x[i] FORALL i \in 0..(N-1))
  TypeOK == (x[i] IN {0,1} FORALL i \in 0..(N-1)) /\ 
            (y[i] IN {0,1} FORALL i \in 0..(N-1))
  Inv == 
    (Cardinality(UNION {x[i] : i \in 0..(N-1)} ) <= 1) /\ 
    (Cardinality(UNION {y[i] : i \in 0..(N-1)} ) <= 1)

=============================================================================
====

CONSTANT N = 8
SPECIFICATION Spec
INVARIANTS PCorrect TypeOK Inv
====