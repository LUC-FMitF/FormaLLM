---- MODULE MCDieHarder ----
moduletype DieHarder

CONSTANTS Goal     =  4
          Jug      =  x \in 1..4 : 4 - x
          Capacity =  y \in 1..4 :
                        IF y \in {1, 2}
                        THEN 2
                        ELSEIF y = 3
                        THEN 3
                        ELSE 4

VARIABLES  s \in {0, 1, 2, 3, 4, 5}
          t \in {0, 1, 2, 3, 4, 5}
          h \in {0, 1, 2, 3, 4, 5}
          m \in {0, 1, 2, 3, 4, 5}
          c \in {0, 1, 2, 3, 4, 5}
          v \in {0, 1, 2, 3, 4, 5}
          b \in {0, 1, 2, 3, 4, 5}
          e \in {0, 1, 2, 3, 4, 5}

SPECIFICATION
Next ==
  \/ \E s \in {0, 1, 2, 3, 4, 5} :
    \E t \in {0, 1, 2, 3, 4, 5} :
      \E h \in {0, 1, 2, 3, 4, 5} :
        \E m \in {0, 1, 2, 3, 4, 5} :
          \E c \in {0, 1, 2, 3, 4, 5} :
            \E v \in {0, 1, 2, 3, 4, 5} :
              \E b \in {0, 1, 2, 3, 4, 5} :
                \E e \in {0, 1, 2, 3, 4, 5} :
                  (h \preceq m /\ m \preceq c /\ c \preceq v /\ v \preceq b /\ b \preceq e /\ e \preceq s)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec ==
  Init \/ [](Next)

INVARIANTS
TypeOK
NotSolved

SPECIFICATION
Spec
====