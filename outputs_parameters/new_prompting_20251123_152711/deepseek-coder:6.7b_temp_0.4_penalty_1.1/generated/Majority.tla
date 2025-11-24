---- MODULE Majority ----
EXTENDS Integer

CONSTANTS MaxLen == 100 (* The maximum length of the sequence *)
VARIABLES seq[0..MaxLen - 1], next, cand, lbnd

(* Definitions used for stating correctness *)
DEFINITIONS
  maj(x) == \A y : Seq [0 .. x] . Cardinality {y} > (Cardinality Seq / 2)

Invariant == (* Inductive invariant for proving correctness *)
    next <= MaxLen - 1 /\
    ~[v : seq[0 .. next] |-> Cardinality {v} > (next + 1) / 2] /\
    maj(next) /\
    cand = IF EXISTS v : seq[0 .. next] . Cardinality {v} - lbnd > 0 THEN
              seq[{v}] ELSE {}

Init == <<>>, next = 0, cand = {}, lbnd = 0

Next == (* Next position of sequence to be checked *)
    IF EXISTS v : seq[next] . Cardinality {v} - lbnd > 0 THEN
      [seq[next + 1], next + 1, seq[next], MAX (Cardinality {seq[next]} - 1, 0)]
    ELSE
      IF next + 1 < MaxLen THEN [seq[next + 1], next + 1, cand, lbnd]
      ELSE Init

Spec == (* Main correctness property: cand can be the only value that has a majority *)
    Init /\ []Next_<<seq, next, cand>>
=============================================================================
====