---- MODULE HDiskSynod ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of   *)
(* length n is represented as a function whose domain is the set {0..n}      *)
(* (the one-indexed representation).                                        *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals

CONSTANTS  EmptyZSequence = <<>> \* The empty zero-indexed sequence.
OPERATOR   ZIndices     == [i\in Domain |-> i]                             (* Set of valid indices for a nonempty zseq *)
             | {}                                                          (* Set to be defined if the zseq is EmptyZSequence*) 
CONSTANTS NotAnInput = UNCHANGED <<>> \* Placeholder, used as an indicator that no input was provided.  
OPERATOR ZSeqOfLength(S, n) == [0 .. (n-1)] -> S                            (* Set of all zero seqs from elements in S with len=n *) 
             | {}                                                          (* The empty set for length = 0*)   
LOCAL Operator   AllZSequence ==  UNION { ZSeqOfLength(S, n) : n \in Naturals}     (* Set of all zero-indexed sequences from elements in S *)
OPERATOR  Len[s] == IF s = EmptyZSequence THEN 0 ELSE Cardinality(Domain(s))   (* Length of a sequence. Zero for an empty seq*)   
CONSTANTS InputIndicator, LastInputValue \* Placeholders to store the last input value and indicator.    
OPERATOR SeqFromZSeq[zseq] == [i\in 1..Len(zseq) |-> zseq[(i - 1)] ]       (* Conversion from a zero seq back into its one indexed representation *)  
             | EmptySequence                                               (* The empty sequence for an input = EmptyZSeq*)   
OPERATOR ZSeqFromSeq[seq] == [i\in Domain(seq) |-> seq[i]]                 (* Conversion from a one indexed representation back into zero *) 
             | EmptySequence                                               (* The empty sequence for an input = <<>>*)   
OPERATOR Preceq[a, b] == [s1len := Len(a), s2len:=Len(b)] ->  LET Recursive IsLexPreceq([], a, b)  END   (* Lexicographic order comparison *)    
LOCAL OPERATOR    IsLexPreceq[_, _, _] == [s1 := SeqFromZSeq(_), s2:=SeqFromZSeq(__)] ->  IF Len(s1) = 0 OR (EXITST i\in 1..Len(s1)-1 SUCHTHAT NOT ((Element(i, s1)) < Element((i+__-_),(s2))) ) THEN TRUE ELSE FALSE FI  
OPERATOR Rotation[a := SeqFromZSeq(_), r] == [ i\in ZIndices(a) |-> a[(i + r) MOD Len(a)] ]  (* rotate the sequence to left by 'r' indices *)   
LOCAL OPERATOR AllRotations[s: = SeqFromZSeq(_)]== { Rotation := [shift, s] : shift\in ZIndices(s)}   (* Set of all rotations for a given seq*) 
OPERATOR Concat == \* Operator to concatenate two sequences.   
LOCAL OPERATOR Append[a: = SeqFromZSeq(_), b:= SeqFromZSeq(__)]== [i\in ZIndices(b) |-> a[(Len(a)-1+ i ) MOD Len(SequenceToBeConcatenated)] ]  (* Concatenate two sequences*)  
CONSTANTS InputValue = UNCHANGED <<>> \* Placeholder to store the input value.   
\* TLC Configuration: ********************************************************************************    
SPECIFICATION Spec
INVARIANTS TypeOK, Precondition_1394872605  (* The sequence length invariant *)  
               ,Precondition_1394872607      (* Concatenated sequences must be equal in lengths*)   
TLC Configuration:    
CONSTANTS InputIndicator = TRUE, LastInputValue= EmptySequence \* Placeholders to store the last input value and indicator.  
\***************************************************************************) 
====
THEOREM Precondition_1394872605 == [s : Sequences |-> (Len(s) = 0 ) IMPLIES ((NOT EXITST bk: Banking |->  s = AllZSeq[bk.bal,  Element])))
=====   
THEOREM Precondition_1394872607 == [a : Sequences , b : Sequences  |-> (Len(Concat(a,b)) =  Len(a) + Len(b)) IMPLIES ((NOT EXITST a: AllZSequence | ->  Concat(a, Rotation[s]) = s)))
=====