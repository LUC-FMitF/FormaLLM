---- MODULE Majority ----

(******************************************************************************)
(* Definitions used for stating correctness.                                 *)
(******************************************************************************)
CONSTANTS   Val,             \* The set of all values.
            Pos              \* Position in the sequence.
            Cand, LB         \* Current candidate and its lower bound respectively.
            Prefix           \* Set of indexes in prefix holding value v.
            CountV, Total    \* Number of times v occurs in that prefix 
                                *and total number of values in sequence respectively.
(******************************************************************************)
VARIABLES  Seq              \* Input sequence of values.

\* The set of all sequences up to some bounded size.
LOCAL BoundedSequence == [0 .. Len - 1] -> Val : Len IN Naturals

(* Main correctness property: cand can be the only value that has a majority *)
Inv(m,n) ==  \E x \in Seq[..<Pos]: Cardinality({i | i \in Pos-Cardinality(Seq), 
                                                    Seq[i] = x}) > m /\
               (Total - m <= n <=> Cand = x /\ LB + Total/2  <= n)

(* Inductive invariant for proving correctness *)
NextInv == Inv((CountV + 1)/2, Cardinality({x | Pos \in Seq[..<Pos], 
                                              (Seq[Pos] = Cand => x = Cand)})) /\
            CountV + Total - m <= Cardinality(Prefix := {i | 0 < i < Pos}) + 1/2 * Total

(* Initialize the algorithm *)
Init == \A x: Seq[x] IN Val  /\  
         Pos = 0           /\   
          Cand = Seq[Pos]  /\    
            LB = 1             /\      
              CountV = 1        /\     
                Total = 1        /\
                  Prefix = {}

(* Algorithm for Boyer-Moore majority vote *)
Next == \E x: Pos + 1 -> Val : 0 < Cardinality(Seq) <= Pos+2  ==> 
            (Cand'= Seq[Pos]    /\ LB' = 1                    /\ CountV' = CountV + IF Seq[Pos'] = Cand THEN 1 ELSE 0 ENDIF     ) \/
             ((CountV - m) * 2 <= Total  ==> (Cand'=Seq[Pos]    /\ LB' = 1                    /\ CountV' = CountV + IF Seq[Pos'] = Cand THEN 1 ELSE 0 ENDIF))     \/
             ((CountV - m) * 2 > Total  ==> (Cand'=Seq[Pos+1]    /\ LB' = 1                    /\ CountV' = 1 + IF Seq[Pos'] = Cand THEN 1 ELSE 0 ENDIF))     \/
             Pos IN BoundedSequence - Cardinality(Prefix) + 2, Total++, Prefix = UNION({i | i <- Pos}, Prefix), m := (CountV+m)/2
              where m is the lower bound of majority. 
              
SPECIFICATION \A x: Seq[x] IN Val /\ Inv(0, Cardinality({y|Pos< y < Len(Seq)})) ==> 
                ABS((Cardinality({i | Pos <= i < Len(Seq), Seq[i] = Cand}) - m)/2 > Total/2 ) 
                ==> EXISTS x: BoundedSequence, Inv(m, Cardinality({y|Pos< y < Len(Seq)})) /\ NextInv  
              
TLC Configuration:
CONSTANTS Val = 0..1    \* The set of all values.
INVARIANTS Pos IN Naturals  /\ Cand IN Val     /\ LB, CountV, Total IN Nat      /\ Prefix SUBSET BoundedSequence  
=============================================================================