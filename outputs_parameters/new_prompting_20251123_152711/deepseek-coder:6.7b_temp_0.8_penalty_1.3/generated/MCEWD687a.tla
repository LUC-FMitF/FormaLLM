---- MODULE MCEWD687a ----

(*******************************************************************************)
(*                                                                             *)
(*                       LAMPORT PAXOS CONSENSUS                               *)
(*                              By lamport                                     *)
(*******************************************************************************)
LOCAL INSTANCE Naturals EXTENDS Model;
LOCAL INSTANCE ZSetoids EXTENDS TLC_Module;
LOCAL INSTANCE Graphs1283940567 EXTENDS Module;
DEFINE LAMPORT = \EagerLamport(Extended);   (* modelParameterConstants *)
CONSTANT Definitions @modelParameterConstants: Procs <- const_163311653400839200;  (* MV CONSTANT definitions *)
(* TLC Configuration *)
\* Constants \*/
CONSTANTS L = {P, P1}, Edges(g) = IF g IN Graphs THEN OutEdges(g) ELSE {}, Leader <- const_163311653400839720; (* MV CONSTANT definitions *)
CONSTRAINT Constr @modelParameterContraint: (G' \in G[Leader] := E'; LTL(ProposeVal, {}))  & \\(\\((P1 = Leader - P) U ((P2 = Leader - P) V (P3 = Leader - P))\\); (* CONSTRAINT definition *)
SPECIFICATION Spec <- LamportSpec;   (* SPECIFICATION definition *)
CHECK_DEADLOCK FALSE;  (* CHECK_DEADLOCK configuration, set to false as deadlock is not expected in this model. *)
(* Invariants \*/
INVARIANT TypeOK(g) & (G[Leader] := E);   (* INVARIANT definition for graph consistency and presence of a leader edge*)
\* Properties Definition \\(\\((P1 = Leader - P2 + P3, |E| = 0)\\)\\), CountersConsistent(&(LamportTimestamp\\_Max[{}] = \*\)), TreeWithRoot; (* PROPERTY definition *)
PROPERTIES CountersConsistent <- NodeCounterProperty & LamportClockIsAncestorOfNodeLabel,  TreeWithRoot <- GraphHasNoCycles(Graphs);   (* Properties Definition for counters consistency and tree structure*)
(* Generated on Fri Oct 01 12:28:54 PDT 2021 *)
\* End of Module LamportPaxos \\(\\)
===============================================================================
====