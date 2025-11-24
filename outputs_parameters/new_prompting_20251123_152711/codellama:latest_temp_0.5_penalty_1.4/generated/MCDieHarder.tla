---- MODULE MCDieHarder ----

(******************************************)
(* The following definitions duplicate the original die hard problem. *)
(*****************************************)
CONSTANTS Goal     =  4                        \* A number of cups to pass in one minute.  (1 <= n < m.)    )
          Jug      <- MCJug                \* An initial amount of water, which must be a non-negative integer; and the capacity is also an positive integers that are at least as large as Goal     *)                        SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====