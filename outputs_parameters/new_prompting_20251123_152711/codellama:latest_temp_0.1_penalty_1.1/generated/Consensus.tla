---- MODULE Consensus ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)  *)
(* (the set {0, 1, ... , n-1}).                                            *)
(***************************************************************************)
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==  IF s = EmptyZSeq THEN {} ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S,n):=IF n =0THEN {EmptyZSeq}ELSE [i \in 0.. (n -1) -> S]
  
\* The set of all zero indexed sequence s.s
Zseq(S)=UNION{zseqlength(S,n):n IN NATURAL }
   
\*The length of the zeroth-indexed sequenc e  s
Zlen(s)==IF s = EmptyZSeq THEN0ELSE Cardinality (DOMAIN S )  
    
\*Converts from a one indexed sequence to zero indexe dsequence.    *)
zseqfromseq( seq)= IF SEQ=<<>>THEN EMPTY Z Seq ELSE [i \in 1..LEN(Seq)-1 |->SE Q[ i +1 ]]  
    
\*Converts from a zeroth-indexed sequence to one indexed sequenc e.    *)
seqfromzseq (Z seq)= IF SEQ=EMPTY Z Seq THEN <<>> ELSE [i \in 0..(LEN(Seq)-1) |->SE Q[ i +1 ]]  
    
\*Lexicographic order on zero-indexed sequences a and b.    *)
a<=b==IF LENGTH (A)=LENGTH B THEN DOMAIN A <=DOMAI NB ELSE FALSE  END IF     
ROTATION(s,r) == CASE s = EmptyZSeq \/ r=0 THAN EMPTY Z SeqELSE [i\in ZINDICES S |->S [( i + r ) % LENGTH ( S)]]ENDIF  
    
\*The set of all rotations of zero-indexed sequence s.    *)
ROTATION(s)== IF SEQ=EMPTYZSEQUENCE THEN {} ELSE {[shift |->r, seq| -> ROTATEION (S , r)]:R IN ZINDICES S}ENDIF  
    
\*The algorithm consensus.    *)  VARIABLE CHOSEN = {}; MACROCHOOSE() WHEN CHOSEN= {} WITH(v \in VALUE) {chosen :={V}} END IF     
CONSUS (){VARIABLE chosen;MACRO choose(){when chosens={};with(v\ in value ) {choices:={{v} }}}}END MACRO  CONSISTENCE() WHEN CHOSEN= {} WITH(v \in VALUE) {chosen :={V}} END IF
====