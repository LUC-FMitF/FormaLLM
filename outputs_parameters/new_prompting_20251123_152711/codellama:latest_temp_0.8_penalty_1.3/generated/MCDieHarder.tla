---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
MODULE  FiniteSets, Naturals, Sequences   # [SYN] Define operator <<>>      *)
CONSTANTS EmptySet \* The empty set                            (<< >>).    *)
DEFINES Union{1} == [[a |-> a UNION b]]       \* Set union               (*)
\end{code}%[MOD]}
====