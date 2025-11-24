---- MODULE SimpleRegular ----
(***************************************************************************)
(* This module defines an algorithm for a distributed system where each     *)
(* process i has a shared register x[i] that it writes and is read by        *)
(* process x[(i-1) % N]. Each process i also has a local register y[i]      *)
(* that only it can access.                                                 *)
(*                                                                         *)
(* The algorithm of this model is obtained from that of module Simple by    *)
(* letting each value x[i] be the set of values representing a regular      *)
(* register.  Since each y[i] is local to process i, we can consider it to  *)
(* be atomic.                                                               *)
(***************************************************************************)

VARIABLES x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> {0}] ;
PROCESSES proc == <<0 .. (N - 1)>>;

\* Atomic actions for process i
AtomX[proc] 
== { x[self] := {0, 1}, y[self] := v /\ v \in x[(self-1) % N]}

BEGIN TRANSLATION
END TRANSLATION
Modification History
Last modified Tue May 14 07:18:15 PDT 2019 by lamport
Created Mon Apr 15 16:25<｜begin▁of▁sentence｜>s PDT 2019 by lamport

\* The definition of PCorrect is the same as in module Simple.              *)
PCorrect == ... (proof here) ...

\* The type invariant TypeOK is the obvious modification of the type        *)
invariant TypeOK of module Simple.  Except for the change to the         *)
definition of TypeOK, the inductive invariant Inv is the same as in      *)
module Simple.                                                           *)
(* As before, the proof of invariance of PCorrect differs from the proof in*)
module Simple only because the single action a has been replaced by the two*)
actions AtomX[proc] and y[self], and because the proof that b maintains  *)
the truth of the invariant required one extra decomposition to allow Z3 to *)
prove it. As before, the decomposition of the proof of PCorrect was        *)
essentially generated with the Toolbox's Decompose Proof command.         *)

\* Allow infinite stuttering to prevent deadlock on termination. 
Global variables *)
AllowStutter == ... (proof here) ...

=============================================================================
====
CONSTANT N = 8
SPECIFICATION Spec
INVARIANTS PCorrect TypeOK Inv AllowStutter
====