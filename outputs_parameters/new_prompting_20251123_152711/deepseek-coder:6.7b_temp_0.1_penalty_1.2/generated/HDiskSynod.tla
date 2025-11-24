---- MODULE HDiskSynod ----

(* Modification History *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai *)
(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of length n is represented as a function whose domain is the set 0..(n-1) (the set {0, 1,..., n-1}). *)
(*******************************************************************************)
CONSTANTS NotAnInput = \* Represents an input that does not exist in our model.
     CHOOSE x : UNIVERSAL - {"NotAnInput"}
     
OPERATIONS IsEmpty(s) == LENGTH[DOMAIN s] = 0, (* Checks if sequence is empty *)
           ZLen(s),                             (* Returns the length of zero-indexed sequences.*) 
           ~ZIndices(s),                         (* Return set of indices for a given nonempty sequence *)
           ~~EmptyZSeq = [],                     (* Empty Sequence Checker Operator *)
           IsNotAnInputAtIndex,                  (* Checks if an index in the domain is not an input.*) 
           ZElement(s),                          (* Returns element at specific Index of a zero-indexed sequence s *)
           ~ZSeqOfLength(* Sequence Generation Operator *)(S, n) = [0 .. (n - 1)] OF UNIVERSAL,  
                                                    (* Creates Zero index sequences with given length and elements from universal set*)
           IsNotAnInputAtIndex(s),               (* Checks if an element in the domain is not an input. *)
           ~ZSeqElementAtIndex(* Element at Index Operator *)(s, i) = IF (i IN DOMAIN s) THEN s[i] ELSE NotAnInput 
                                                    (* Returns a specific indexed value from sequence or 'NotAnInput' if the index is not in domain *)  
           ~ZSeq(S),                             (* Creates all possible zero-index sequences with elements of universal set S*)
           ZIndices,                            (* Return indices for nonempty sequence s. *)(s) = IF (LENGTH[DOMAIN s] = 0) THEN {} ELSE DOMAIN s 
           ~ZLen(s),                             (* Returns the length of zero-indexed sequences *)  
                                                   
LOCAL INSTANCE FiniteSets, Naturals, Sequences   
\* TLC Configuration: *)(CONSTANTS NotAnInput = CHOOSE x : UNIVERSAL - {"NotAnInput"}) 
====(* CONFIGURATION (bk.bal = 0) IMPLIES (bk.inp = NotAnInput)) *)  
\* Specification: *)(SPECIFICATION IsEmpty(s) => ZLen(~ZIndices(s)) = 0 AND ~IsNotAnInputAtIndex(DOMAIN s), 
                      (* If sequence is not empty, then indices are in domain and element at index i of a nonempty sequence equals to the value if it exists or 'NotAnInput' otherwise *)  
                      ~ZSeqElementAtIndex(s, ZIndices(s)) = IF (LENGTH[DOMAIN s] = 0) THEN NotAnInput ELSE ~ZLen(s)*)( 
\* Invariants: *)(INVARIANTS IsEmpty(s), ZLen(s), ZSeqOfLength(* Sequence Generation Operator *)~ZIndices(s))  
=============================================================================