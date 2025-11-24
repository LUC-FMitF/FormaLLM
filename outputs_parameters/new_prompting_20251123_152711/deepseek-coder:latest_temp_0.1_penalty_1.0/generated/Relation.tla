---- MODULE Relation --------

(***************************************************************************)
(* This module provides some basic operations on relations, represented as     *)
(* binary Boolean functions over some set S.                             *)
(***************************************************************************)

CONSTANTS S

LOCAL INSTANCE R

\* The relation R is reflexive over S?
Reflexive(R, S) ==
  FORALL x  IN S : R[x, x]

\* The relation R is irreflexive over set S?
Irreflexive(R, S) ==
  FORALL x  IN S : ¬R[x, x]

\* The relation R is symmetric over set S?
Symmetric(R, S) ==
  FORALL x, y  IN S : IF R[x, y] THEN R[y, x]

\* The relation R is asymmetric over set S?
Asymmetric(R, S) ==
  FORALL x, y  IN S : IF R[x, y] AND R[y, x] THEN x = y

\* The relation R is transitive over set S?
Transitive(R, S) ==
  FORALL x, y, z  IN S : IF R[x, y] AND R[y, z] THEN R[x, z]

\* Compute the transitive closure of relation R over set S.
TransClosure(R, S) ==
  IF R  reflexive  over  S
  THEN R
  ELSE 
    FORALL P  IN Pow(S, 2) :
      IF P  transitive  over  S
      THEN R  P
      ELSE 
        FORALL x  IN S :
          IF R[x, P[1]]  AND  R[P[1], P[2]]
          THEN R  P
          ELSE 
            FORALL x  IN S :
              IF R[x, P[1]]  AND ¬R[P[1], P[2]]
              THEN R  P
              ELSE 
                Empty

\* Compute the reflexive transitive closure of relation R over set S.
ReflexTransClosure(R, S) ==
  IF R  reflexive  over  S
  THEN TransClosure(R, S)
  ELSE 
    FORALL x  IN S :
      IF R[x, x]
      THEN ReflexTransClosure(R, S)
      ELSE 
        FORALL x, y  IN S :
          IF R[x, y]  AND ¬R[y, x]
          THEN ReflexTransClosure(R, S)
          ELSE 
            Empty

\* Is the relation R connected over set S, i.e. does there exist a path *)
(* between two arbitrary elements of S?                            *)
Connected(R, S) ==
  FORALL x, y  IN S : IF R[x, y] OR R[y, x] THEN x = y

=============================================================================
====