---- MODULE TLAPS ----
(* TLA+ code for setting up various backend provers and rules *)

EXTENDS TLC

CONSTANTS
  -- SMT solver pragmas
  + "smt3" : STRING
  + "cvc33" : STRING
  + "yices3" : STRING
  + "verit" : STRING
  + "z33" : STRING
  + "spass" : STRING
  -- Propositional linear time temporal logic prover pragmas
  + "ls4" : STRING
  -- Automatic theorem proving pragmas
  + "zenon" : STRING
  + "isabelle" : STRING

OPERATIONS
  -- Backend pragma operations
  + By(prover:STRING) = prover
  + ByTimeout() = "timeout @"

DERIVED CONSTANTS
  -- Multi-back-ends pragmas
  + MultiBackends = By("cvc33") \ {By(prover) | prover <- [SMT solvers]}
                   /\ ByTimeout() @ SMT solvers

ASSUMPTIONS
  1. EXTENDS TLC
====