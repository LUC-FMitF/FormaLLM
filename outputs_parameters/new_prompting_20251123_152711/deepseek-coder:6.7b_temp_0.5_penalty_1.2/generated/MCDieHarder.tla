---- MODULE MCDieHarder ----

(**************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(**************************************************************************)
MODULE ZSequences EXTENDS TLC;
\* The empty zero-indexed sequence *%/ EmptyZSeq == <<>> /\ *The set of valid indices for zero-indexed sequence s *%/ 
    ZIndices(s) ==  IF s = EmptyZSeq THEN {} ELSE DOMAIN s \*\*/\ AndAlso (* The length of zero-indexed sequence s *) 
        ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s) /\ *Converts from a one-indexed sequence to a zero-indexed sequence*) 
    ZSeqFromSeq(seq) ==  IF seq = <<>> THEN EmptyZSeq ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]] /\ *Converts from a zero-indexed sequence to a one-indexed sequence*)
    SeqFromZSeq(zseq) ==  IF zseq = EmptyZSeq THEN <<>> ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]] /\ *Lexicographic order on zero-indexed sequences a and b*)
    a <=b == LET s1len ==  ZLen(a) AND s2len ==  ZLen(b) RECURSIVE IsLexLeq(_, _, _)(s1, s2, i)== CASE  (i = s1len /\ i = s2len -> s1len <= 
    Goal == MCCapacity[j \in 0..Goal |->  j] /. MCJug == 4 AND a <= b IMPLIES NOT(b < a) FORALL [a, b EQCLASS {MCJug}] ENDDEFINITIONS DEFINE CONSTANTS
    MCCapacity[j \in 0..Goal |->  j * MCJug] /\ NotSolved == EXISTS [x IN ZIndices(Capacity)] NOT Solved[x, Capacity) AND (NOT x < Goal OR Exists [y IINZIndi
    ces(Capacity)]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXISTS [n IN ZIndices(MCCapacity)](Solved[n, MCCapacity]) /\ TypeOK
    NOT Solved FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE INVARIANTS TypeOK == [j \in ZIndices(MCCapacity) |-> Capacity[j] = j * MCJu
    g ] /\ NotSolved ==  EXISTS[x, y  EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists[z INZ Indices(Capacity)] z > Goal ) ENDDEFINITIONS DEFINE CONSTANTS MCCap
    acity == [j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved ==  EXISTS[x, y  EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists[z INZ Indices(C
    apacity)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXISTS [n IN ZIndices(MCCapacity)](Solved[n, MCCapacity]) /\ TypeOK NOT Solved FORA
    LL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTANTS MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCCapacity)] NO T
    solved[x, MCCapacity) AND (NOT x < Goal OR Exists [y IINZIndi ces(Capacity)]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capacity == MC
    Capacity[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved ==  EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces
    (Capacity)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXISTS [n IN ZIndices(MCCapacity)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv
    ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTANTS MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCCapa
    city)] NOT Solved[x, MCCapacity) AND (NOT x < Goal OR Exists [y IINZ Indi ces(Capacity)]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS C
    apacity == MCJCApacity[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved ==  EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exi
    sts [z INZ Indices(Capacity)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXISTS [n IN ZIndices(MCCapaci
    ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTANTS MCJug == 4 AndA
    o Also NotSolved == EXISTS [x IN ZIndices(MCCapacity)] NOT Solved[x, MCCapaci ty) AND (NOT x < Goal OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capacity == MCJCApacity[j \in ZIndices(MCCapaci ty) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit
    y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXISTS [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORA
    LL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTANTS MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCCapaci ti y) ]
     NOT Solv ed[x, MCCapacity) AND (NOT x < Goa l OR Exists [y IINZ Indi ces(Capacit
    y)]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capacity == MCJCApaci ty[j \in ZIndices(MCCapaci ty) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capa ci ty)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NTS MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCCapaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capac
    it y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI
    STs [n IN ZIndices(MCCapaci ty)](Solved[n, MCCapacity]) /\ TypeOK NOT Solv ed FORALL n \in Naturals STARTS 0 AND STEPS Goal ENDDEFINITIONS DEFINE CONSTA
    NT MCJug == 4 AndAlso NotSolved == EXISTS [x IN ZIndices(MCC apaci ty)] NOt Solved[x, MCCapacity) AND (NOT x < G o a l OR Exists [y IINZ Indi ces(Capacit
    y}]  y >=0 AND 2*y <=Goal ) ENDDEFINITIONS DEFINE CONSTANTS Capaci ty == MCJCApa ci ty[j \in ZIndices(MCCapacity) |-> j * MCJug] /\ NotSolved
    == EXISTS [x, y EQCLASS {MCJug}] (Capacity[y]- x = 0 OR Exists [z INZ Indi ces(Capacit y)] z > Goal ) ENDDEFINITIONS DEFINE SPECIFICATION Spec == EXI'''

# 중복을 허용하거나, 제거해주는 set() 활용. list(set()) 후 len() 통해 중복을 제거
# Counter 사용 -> dict type, most_common method : [('a',3), ('b',2)]... => a:3 b:2 ...
from collections import Counter
import re

def solution(s):
    s =Counters=Counter(re.findall("[a-z]+",S)) # 단어의 개수 count, [a-z] : a~z (lowercase) + (1 or more), find all -> list
    return s.most_common(1)[0][0]   # most common word => the first element of the tuple => the key part of the tuple 
print(solution("a,b"))'''

# 정규표현식이란? : Regular Expression. 여러 메타 문자와 패턴을 이용, 검색(find), 치환(replace)
# \d : [0-9] (digit), + : one or more. re.findall("[a-z]+",S) -> S라는 string을 'a~z'가 1개 이상 => list type
# Counter()함수? : collections module, dict subclass. element를 key로 count 결과 return (dict) -> {element:count}...
====