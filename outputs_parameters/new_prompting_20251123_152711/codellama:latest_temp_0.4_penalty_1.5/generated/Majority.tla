---- MODULE Majority ----

(***************************************************************************
* TLA+ specification and proof of the majority vote algorithm due to Boyer *)
AND Moore.                                                                *
R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.          *
In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody      *
Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                  *
Originally published as a technical report from 1981.                    *
The algorithm takes as input a sequence of values, makes one pass over   *
the sequence, and reports an element cand such that no element other     *
than cand may have an absolute majority in the sequence.                 *)
***************************************************************************)
(* The following definitions are used for stating correctness:            *)
(***************************************************************************
* A value v is a candidate if it has at least floor((n+1)/2) occurrences  *
in seq, and no other element can have more than ceil((n-1)/2)             *
occurrences in the prefix of seq strictly before j.                      *)
(***************************************************************************
* A value v is a candidate if it has at least floor((n+1)/2) occurrences  *
in seq, and no other element can have more than ceil((n-1)/2)             *
occurrences in the prefix of seq strictly before j.                      *)
(***************************************************************************)
(* A value v is a candidate if it has at least floor((n+1)/2)     *)
Candidate == <<v: Occurrence[seq] /\ (Occurrence[prefix]) <=> 0>>   *
              \/ ((Occurrence[prefix]) = ceil(n-1))                    *)
(* A value v is a candidate if it has at least floor((n+1)/2)     *)
Candidate == <<v: Occurrence[seq] /\ (Occurrence[prefix]) <=> 0>>   *
              \/ ((Occurrence[prefix]) = ceil(n-1))                    *)
(* A value v is a candidate if it has at least floor((n+1)/2)     *)
Candidate == <<v: Occurrence[seq] /\ (Occurrence[prefix]) <=> 0>>   *
              \/ ((Occurrence[prefix]) = ceil(n-1))                    *)
***************************************************************************)
====