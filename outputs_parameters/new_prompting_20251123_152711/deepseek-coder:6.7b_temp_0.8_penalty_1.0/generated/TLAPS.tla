---- MODULE TLAPS ----
(* TLAPS Configurations *)
\* Backend pragmas *\)
{ by (prover:"smt3") }
{ by (prover:"cvc33") }
{ by (prover:"yices3") }
{ by (prover:"z33") }
{ by (prover:"isabelle"; tactic:"auto") }  (* Isabelle's automatic search *)
{ by (prover:"isabelle"; tactic:"blast") }  (* Isabelle's tableau prover *)
(* Temporal Logic *)
\* The following rules are intended to be used when TLAPS handles temporal logic. *\)
\* They will not work now. Moreover, when temporal reasoning is implemented, *\)
\* these rules may be changed or omitted, and additional rules will probably be added. *\)
\* However, they are included mainly so their names will be defined, preventing the use *\)
\* of identifiers that are likely to produce name clashes with future versions of this module. *\)
====