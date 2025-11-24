---- MODULE Relation ----
EXTENDS TLC

CONSTANTS
  S,
  R

ASSUME
  R \in POWERSET(S) \* R is a relation over S

VARIABLES
  transitiveClosure,
  reflexiveTransitiveClosure

DEFINE
  Reflexive == \* Is the relation R reflexive over S?
    \A x \in S : R(x, x)

  Irreflexive == \* Is the relation R irreflexive over set S?
    \A x \in S : ~R(x, x)

  Symmetric == \* Is the relation R symmetric over set S?
    \A x, y \in S : R(x, y) => R(y, x)

  Asymmetric == \* Is the relation R asymmetric over set S?
    \A x, y \in S : R(x, y) => ~R(y, x)

  Transitive == \* Is the relation R transitive over set S?
    \A x, y, z \in S : R(x, y) AND R(y, z) => R(x, z)

  TransitiveClosure == \* Compute the transitive closure of relation R over set S.
    \A x, y \in S : R(x, y) OR transitiveClosure(x, y)

  ReflexiveTransitiveClosure == \* Compute the reflexive transitive closure of relation R over set S.
    \A x, y \in S : R(x, y) OR reflexiveTransitiveClosure(x, y) OR (x = y AND \A z \in S : R(x, z))

  Connected == \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    \A x, y \in S : (x, y) \in (transitiveClosure \cup reflexiveTransitiveClosure)

SPECIFICATION
  Reflexive => Transitive
  Symmetric => Transitive
  Asymmetric => Transitive
  Transitive => Connected

INVARIANTS
  TypeOK

TLC
  CONFIG
    FORMAT = "TLA+"
    MODULE = "RelationProperties"
    INITIAL = "Reflexive"
    NEXT = "TransitiveClosure,ReflexiveTransitiveClosure"
    PROPERTY = "Connected"
====