---- MODULE TLAPS ----
(* This is an example TLA+ module, which utilizes various backends and includes some comments about the usage of different pragmas *)
MODULE EXAMPLE
EXTENDS TLC
BEGIN
    CONSTANTS
        SetExtensionality : BOOLEAN
      = TRUE; (* THEOREM   \A S, T ∈ SET: (S = T) <=> (\A x ∈ S) <=> (x ∈ T) *)

    -- Backend pragmas
    PRAGMA by prover:"smt3"; (* use the SMT solver for arithmetic. Default timeout is 5 seconds *)
    PRAGMA by prover:"cvc33"; (* CVC3 SMT solver *)
    PRAGMA by prover:"yices3"; (* Yices SMT solver *)
    PRAGMA by prover:"z33"; (* Z3 SMT solver *)
    PRAGMA by prover:"isabelle"; tactic:"auto"; (* Isabelle with automatic search "auto" and default timeout 30 seconds *)
    PRAGMA by (prover:"cvc33"; timeout:120); (* CVC3 SMT solver with timeout of 120 seconds *)
    -- Backend pragmas for multi-back-ends, runs one after the other in hope that one will succeed
    PRAGMABY
        prover:"cvc33",
        prover:"smt3",
        prover:"yices3",
        prover:"z33";
END.
====