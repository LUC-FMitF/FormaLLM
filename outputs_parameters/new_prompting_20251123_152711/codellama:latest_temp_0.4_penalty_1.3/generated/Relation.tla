---- MODULE Relation ----

(***********************************************************************
* This module provides some basic operations on relations, represented  *
as binary Boolean functions over some set S.                            *
************************************************************************)
CONSTANTS   R,    \* The relation to operate upon.
            S     \* The underlying set of the relation.
VARIABLES   r_refl,       \* Is the relation reflexive over S?
            r_irrel,      \* Is the relation irreflexive over S?
            r_symm,       \* Is the relation symmetric over S?
            r_asymm,      \* Is the relation asymmetric over S?
            r_trans,      \* Is the relation transitive over S?
            Rtclosure     \* The reflexive-transitive closure of R.
-------------------------------------------------------------------------
r_refl == /\ ![x |-> x :in R] => [x |-> TRUE:in S] = R   * Is the relation reflexive over S?
    /\ ![y \in S, z \in S | (R(z)(y) & y /= z)]                      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be reflexive-transitive over S.
    /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]                      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be reflexive-transitive over S.
-------------------------------------------
r_irrel == /\ ![y \in S, z \in S | (R(z)(y) & y /= z)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be irreflexive over S.
------------------------------
r_symm == /\ ![x \in S, y \in S | (R(y)(z) & z /= x)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be symmetric over S.
------------------------------
r_asymm == /\ ![x \in S, y \in S | (R(y)(z) & z /= x)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be asymmetric over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
------------------------------
r_trans == /\ ![x \in S, y \in S | (R(y)(z) & z /= y)]      * If there is a path from x to itself in R.
        => [x :-> TRUE] = Rtclosure   * Then the relation must be transitive over S.
----------------
====