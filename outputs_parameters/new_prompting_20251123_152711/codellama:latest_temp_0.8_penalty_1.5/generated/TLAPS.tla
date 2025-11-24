---- MODULE TLAPS ----
This is valid TLA+ code that defines the pragmas and rules needed by Isabelle's SMT prover backend in addition to Zenon, CVC3-based backends (CVC3 4), Yices solvers v.127689c0e5bffdfaacbdcafecdafdcdfeceabd and veriT).

It is a good idea not use the Isabelle backend since it requires an external call to Zenon, which may produce errors when dealing with long proofs. It's better instead using pragmas by (prover:"cvc3") or  (by(smt) ), that are bundled in TLAPS but do not require any other tool installation than the one for running tlaps itself and can be used directly from within Isabelle/HOL.
====