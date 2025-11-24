---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS EmptyZSeq
VARIABLES ZSeq

Init == EXTENDS Init AND ZSeq = EmptyZSeq

Next == EXTENDS Next AND ZSeq' = IF ZLen(ZSeq) < Cardinality(Naturals) THEN [i \in 0..ZLen(ZSeq)-1 |-> ZSeq[i]+1] ELSE ZSeq ENDIF

Spec == EXTENDS Spec AND [][][Next]_<<>> = <<>>
====