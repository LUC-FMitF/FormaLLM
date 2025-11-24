---- MODULE Majority ----

(***************************************************************************)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.          *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody      *)
(* Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                 *)
(* Originally published in a technical report from 1981.                    *)
(*                                                                         *)
(* Although seq is an input to the algorithm, we make it a variable so that *)
(* we can use the model checker to verify the algorithm for all sequences   *)
(* up to some bounded size.                                                  *)
(***************************************************************************)

CONSTANTS
  EmptySet == {}
  One        == {{}}

Variables
  seq    /\seq \in SeqOf(Val) ** sequence of values, never changes
  pos    /\pos   \in Nat       ** next position of sequence to be checked
  cand   /\cand  \in Val        ** current candidate for having a majority
  lower  /\lower \in Nat       ** lower bound for the number of occurrences of the candidate so far

Defines
  SeqOf(Val) == UNION {EmptySet} UNION [n \in Nat -> Val]

Assignments
  /\init   == <<>>, 0, EmptySet, pos = 1, cand = seq[0], lower = 0
  /\update == IF pos < Len(seq)
               THEN (cand', lower') /\nextPos(pos + 1), IF pos > 0 AND cand \= seq[pos] THEN cand' = seq[pos], lower' = LOWER(seq, Val -> Pos + Cand -> Lower - 1) ELSE cand', lower'
  /\next   == (cand'', lower'') /\update IF pos = 0, cand'' = EmptySet, lower'' = 0
  /\inv    == cand \in Dom(seq) IFF lower + Cardinality([n \in Nat -> seq[n] = cand]) > Len(seq)/2

=============================================================================
====
TLC Configuration:

CONSTANTS
  SeqSize == 10 ** The size of the sequence to be checked by TLC

SPECIFICATION Inv
====