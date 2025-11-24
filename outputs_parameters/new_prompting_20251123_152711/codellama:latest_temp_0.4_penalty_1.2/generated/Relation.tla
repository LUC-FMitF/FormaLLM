---- MODULE Relation ----

(*************************************************************************)
(* This module provides some basic operations on relations, represented  *)
* as binary Boolean functions over some set S.                            *)
(*************************************************************************)

CONSTANTS   R,    \* The relation to operate on.
            S     \* The underlying set of the relation.
VARIABLES   r,    \* A function representing the relation R over S.
            s     \* An element from S.
-----------------------------------------------------------------------------
IsReflexive(R) ==  \* Is the relation R reflexive over set S?                 *)
    /\ ![s \in S |-> r[s, s]]   \* The relation is not reflexive if there exists an element s in S such that r[s, s] = FALSE.
-----------------------------------------------------------------------------
IsIrreflexive(R) ==  \* Is the relation R irreflexive over set S?             *)
    /\ ![\A s \in S |-> r[s, s]]   \* The relation is not irreflexive if there exists an element s in S such that r[s, s] = TRUE.
-----------------------------------------------------------------------------
IsSymmetric(R) ==  \* Is the relation R symmetric over set S?                 *)
    /\ ![\A s1, s2 \in S |-> (r[s1, s2] <=> r[s2, s1])]   * The relation is not symmetric if there exists an element s1 and an element s2 in S such that r[s1, s2] = FALSE and r[s2, s1] = TRUE.
-----------------------------------------------------------------------------
IsAsymmetric(R) ==  \* Is the relation R asymmetric over set S?         *)
    /\ ![\A s1, s2 \in S |-> (r[s1, s2] <=> r[s2, s1])]   * The relation is not asymmetric if there exists an element s1 and an element s2 in S such that r[s1, s2] = TRUE and r[s2, s1] = FALSE.
-----------------------------------------------------------------------------
IsTransitive(R) ==  \* Is the relation R transitive over set S?         *)
    /\ ![\A s1, s2, s3 \in S |-> (r[s1, s2] /\ r[s2, s3]) => r[s1, s3]]   * The relation is not transitive if there exists an element s1 and two elements s2 and s3 in S such that r[s1, s2] = TRUE and r[s2, s3] = TRUE but r[s1, s3] = FALSE.
-----------------------------------------------------------------------------
TransClosure(R) ==  \* Compute the transitive closure of relation R over set S. *)
    [s \in S |-> {r' | r' \subseteq R /\ ![\A x, y \in s |-> (x = y <=> r[x, y])]}]   * The transitive closure is a function from S to the power set of R. Each element in this function represents the transitive closure of relation R over an element s in S.
-----------------------------------------------------------------------------
ReflexiveTransClosure(R) ==  \* Compute the reflexive transitive closure of relation R over set S. *)
    [s \in S |-> {r' | r' \subseteq TransClosure(R)[s] /\ ![\A x, y \in s |-> (x = y <=> r[x, y])]}]   * The reflexive transitive closure is a function from S to the power set of R. Each element in this function represents the reflexive transitive closure of relation R over an element s in S.
-----------------------------------------------------------------------------
IsConnected(R) ==  \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S? *)
    /\ ![\A s1, s2 \in S |-> (s1 = s2 <=> EXISTS x \in S : r[x, s1] /\ r[x, s2])]   * The relation is not connected if there exists an element s1 and an element s2 in S such that there does not exist a path between them.
-----------------------------------------------------------------------------
THEOREM IsReflexive(R) <=> ![\A x \in S |-> r[x, x]]   * The relation is reflexive if it satisfies the following property: for all elements x in S, there exists an element y such that r[y, y] = TRUE.
-----------------------------------------------------------------------------
THEOREM IsIrreflexive(R) <=> ![\A x \in S |-> r[x, x]]   * The relation is irreflexive if it satisfies the following property: for all elements x in S, there does not exist an element y such that r[y, y] = TRUE.
-----------------------------------------------------------------------------
THEOREM IsSymmetric(R) <=> ![\A s1, s2 \in S |-> (r[s1, s2] /\ r[s2, s1]) => FALSE]   * The relation is symmetric if it satisfies the following property: for all elements s1 and s2 in S such that r[s1, s2] = TRUE and r[s2, s1] = TRUE, there exists an element x such that r[x, y] = TRUE.
-----------------------------------------------------------------------------
THEOREM IsAsymmetric(R) <=> ![\A s1, s2 \in S |-> (r[s1, s2] /\ r[s2, s1]) => FALSE]   * The relation is asymmetric if it satisfies the following property: for all elements s1 and s2 in S such that r[s1, s2] = TRUE and r[s2, s1] = TRUE, there does not exist an element x such that r[x, y] = FALSE.
-----------------------------------------------------------------------------
THEOREM IsTransitive(R) <=> ![\A s1, s2, s3 \in S |-> (r[s1, s2] /\ r[s2, s3]) => r[s1, s3]]   * The relation is transitive if it satisfies the following property: for all elements s1 and two elements s2 and s3 in S such that r[s1, s2] = TRUE and r[s2, s3] = TRUE but r[s1, s3] = FALSE.
-----------------------------------------------------------------------------
THEOREM TransClosure(R) <=> ![\A x \in S |-> {r' | r' \subseteq R /\ ![\A y \in x |-> (y = z <=> r[x, y])]}]   * The transitive closure is a function from S to the power set of R. Each element in this function represents the transitive closure of relation R over an element s in S.
-----------------------------------------------------------------------------
THEOREM ReflexiveTransClosure(R) <=> ![\A x \in S |-> {r' | r' \subseteq TransClosure(R)[x] /\ ![\A y \in x |-> (y = z <=> r[x, y])]}]   * The reflexive transitive closure is a function from S to the power set of R. Each element in this function represents the reflexive transitive closure of relation R over an element s in S.
-----------------------------------------------------------------------------
THEOREM IsConnected(R) <=> ![\A s1, s2 \in S |-> (s1 = s2 <=> EXISTS x \in S : r[x, s1] /\ r[x, s2])]   * The relation is connected if there exists an element s1 and an element s2 in S such that there does not exist a path between them.
-----------------------------------------------------------------------------
====