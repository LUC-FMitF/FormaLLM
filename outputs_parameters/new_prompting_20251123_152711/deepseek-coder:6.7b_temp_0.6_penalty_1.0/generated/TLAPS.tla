---- MODULE TLAPS ----
(*
Backend pragmas.  *)
MODULE BackendPragmas
VARIANT
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE bySMT,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY bySMT,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byCVC3,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byCVC3,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byYices,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byYices,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byVerit,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byVerit,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byZ3,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byZ3,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelle,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelle,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleAuto,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleAuto,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleForce,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleForce,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleSetEqual,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleSetEqual,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleClarsimpAuto,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleClarsimpAuto,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleClarsimp,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleClarsimp,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleAutoBlast,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleAutoBlast,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  USE byIsabelleMultiBackends,
  (* The pragma that is added to the context of an obligation most recently is the one whose effects are triggered. *)
  BY byIsabelleMultiBackends
END BackendPragmas

(* Temporal Logic *)
MODULE TemporalLogic
VARIANT
  (* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained from the following two rules by the following substitutions: `. *)
  USE WF2,
  (* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained from the following two rules by the following substitutions: `. *)
  BY WF2,
  (* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained from the following two rules by the following substitutions: `. *)
  USE SF2,
  (* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained from the following two rules by the following substitutions: `. *)
  BY SF2,
  (* The following rule is a special case of the general temporal logic proof rule STL4 from the paper "The Temporal Logic of Actions". The general rule is for arbitrary temporal formulas F and G, but it cannot yet be handled by TLAPS. *)
  USE STL4,
  (* The following rule is a special case of rule TLA2 from the paper "The Temporal Logic of Actions". *)
  BY TLA2,
  (* The following may be used to invoke a decision procedure for propositional temporal logic. *)
  USE TemporalDecisionProcedure
END TemporalLogic
====