---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal value for the game.
    == 4

CONSTANTS Jug      \* The capacity of the jug.
    == 3

CONSTANTS Capacity \* The capacity of the jug.
    == [j \in 0..Jug |-> j]

VARIABLES   m, n, p, q, r, s, t, u, v, w, x, y, z : Nat

Init ==
    /\ m = 0
    /\ n = 0
    /\ p = 0
    /\ q = 0
    /\ r = 0
    /\ s = 0
    /\ t = 0
    /\ u = 0
    /\ v = 0
    /\ w = 0
    /\ x = 0
    /\ y = 0
    /\ z = 0

Next ==
    \/ \E m, n, p, q, r, s, t, u, v, w, x, y, z :
        (m < Goal /\ n < Goal /\ p < Goal /\ q < Goal /\ r < Goal /\ s < Goal /\ t < Goal /\ u < Goal /\ v < Goal /\ w < Goal /\ x < Goal /\ y < Goal /\ z < Goal)
        /\ (m + n + p + q + r + s + t + u + v + w + x + y + z = Capacity)
        /\ (m + n + p + q + r + s + t + u + v + w + x + y + z < Goal)

Spec == Init /\ [][Next]_<<m, n, p, q, r, s, t, u, v, w, x, y, z>>

=============================================================================
====