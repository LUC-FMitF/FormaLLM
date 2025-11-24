---- MODULE HDiskSynod -----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS NotAnInput = \* A constant representing an input that does not exist.
     CHOOSE x : NOT EXISTS y: x=y
     
LOCAL INSTANCE FiniteSets  (* Local instance of the set abstraction *)
LOCAL INSTANCE Naturals   (* Local instance of the natural numbers *)
LOCAL INSTANCE Sequences  (* Local instance of sequences *)
    
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == 
   IF s = EmptyZSeq THEN {} ELSE DOMAIN s  (* Returns the domain if not an empty sequence *)
   
\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S,n) ==
   IF n=0 THEN {EmptyZSeq}                   (* Empty sequence for 0 length *)
   ELSE [i \in 0..<n :-> CHOOSE x:x IN S]     (* A function from domain to set elements *)
   
\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION { ZSeqOfLength(S, n): n \in Nat }  (* Union over natural numbers *)
  
\* The length of zero-indexed sequence s
ZLen(s) ==  IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)    (* Length is cardinality of domain if not empty, else return 0*)
    
\* Converts from a one-indexed sequence to a zero-indexed sequence  
ZSeqFromSeq(seq) ==  IF seq = <<>> THEN EmptyZSeq ELSE [i \in DOMAIN seq : -> seq[i]]  (* Substitute i with value at index *)
   
\* Converts from a zero-indexed sequence to a one-indexed sequence  
SeqFromZSeq(zseq) ==  IF zseq = EmptyZSeq THEN <<>> ELSE [i \in DOMAIN zseq : -> zseq[i]]  (* Substitute i with value at index *)
   
\* Lexicographic order on zero-indexed sequences a and b  
a <=_lex b == LET s1len = ZLen(a),s2len=ZLen(b) IN EXISTS x \in [0..<Min[s1len,s2len]](a[x]\neq b[x]) OR (s1len\leq s2len AND a <=_lex b ) (* Lexicographic order defined *)
   
\* Rotate the string s to the left by r indices  
Rotation(s,r) ==  IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in DOMAIN s : -> s[(i+r)\% ZLen(s)]] (* Apply rotation formula *) 
   
\* The set of all rotations of zero-indexed sequence s  
Rotations(s) ==  IF s = EmptyZSeq THEN {} ELSE { [shift \in DOMAIN s : -> r, seq[i]\in Rotation(r)] } (* Set comprehension for each rotation *) 
   
=============================================================================
CONSTANTS bk.bal = 0  == (bk.inp = NotAnInput) *\     (* TLC Configuration: Constants and Specification*)
SPECIFICATION [~](ZLen(Rotation([i \in Nat : -> ch], i))= ZLen(ch))    (* The length of a rotation is the same as original sequence *) 
INVARIANTS TypeOK, FiniteSetOK, SequenceOK  == (bk.bal = 0) /\ (bk.inp = NotAnInput)*     (* Invariants: Ensuring types and sets are finite*)
=====