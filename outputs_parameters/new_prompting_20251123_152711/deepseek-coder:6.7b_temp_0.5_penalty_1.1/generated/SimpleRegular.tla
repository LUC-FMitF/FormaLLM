---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module is a generalization of the algorithm in module Simple.       *)
(* It assumes that each shared register x[i] is a regular register, which    *)
(* can be read and written by any process but only at an atomic step.        *)
(* Each local register y[i] is assumed to be atomic as well.                 *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
CONSTANT N 

VARIABLE x == [i \in 0..N-1 |-> {0}]
VARIABLE y == [i \in 0..N-1 |-> {0}]

\* The atomic action of each process i writing to its shared register x[i]
LOCAL ActionX(proc) == 
  x[proc] := {0, 1} // Update the value of x[proc] to be either 0 or 1

\* The atomic action of each process i reading from the previous processes's shared register x[(i-1) % N]
LOCAL ActionY(proc) == 
  with (v \in x[(proc - 1) % N]) // v is the value read from x[(proc - 1) % N]
    y[proc] := v                 // Update the local register y[proc] to be v

\* The process i of this algorithm
PROCEDURE (proc \in 0..N-1) ==
  ActionX(proc),
  ActionY(proc)

=============================================================================
====
(* CONFIGURATION FOR TLC *)
CONSTANTS N = 8
SPECIFICATION Spec
INVARIANTS PCorrect TypeOK Inv
====