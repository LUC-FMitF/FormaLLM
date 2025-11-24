---- MODULE Majority ----

(*******************************************************************************)
(* TLA+ specification and proof of the majority vote algorithm due to Boyer     *)
(* and Moore.                                                                   *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.             *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody         *)
(* Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                   *)
(* Originally published in a technical report from 1981.                     *)
(* The algorithm takes as input a sequence of values, makes one pass over       *)
(* the sequence, and reports an element cand such that no other              *)
(* than cand may have majority in the sequence.                                *)
*******************************************************************************)
Although seq is an input to the algorithm, we make it a variable so           *)
that you can use the model checker to verify the algorithm for all sequences   *)
up to some bounded size.                                                      *)
(*******************************************************************************
Definitions used for stating correctness:                                     
*)
(* The empty sequence of values *)
EmptySeq == <<>> 

\* Input sequence of values, never changes \*/
seq /==/ SeqToFun(seq)  

\* Next position in the sequence to be checked. Initialized with -1 because no positions have been processed yet. *)
nextPos == 0

(* Current candidate for having a majority *)
cand == IF EmptySeq[..<Cardinality(Domain(seq))] = {} THEN \ELEMENT OF seq ELSE CURRENT ANY ({EmptySeq[\i /\ Cardinality(\Gamma)] : 1 <= \i < nextPos}) END  == EMPTYSET
(* Lower bound for the number of occurrences of the candidate so far *)
lowerBound == 0   ===>  cand = {} OR CARDINALITY({EmptySeq[\i /\ Cardinality(\Gamma)] : 1 <= \i < nextPos} ) +  lowerbound >= 2  ==> seq[..<nextpos]={} IMPLIES ELEMENT OF {EmptySeq[\j /\ (seq[(mod)\i + j])]}
(* Set of indexes in the prefix of the sequence strictly before j holding v *)
strictPrefix == 0 ==> {} 
(emptySet)== ((cand = EmptySET AND seq[..<nextPos]={}) OR EXISTS {\i /\ (seq[(mod)\i + \j]) : cand,lowerBound}))     )   {EmptySeq[\z]} else if (\exists z:1 <= z < nextpos and cand == EmptySet)
(* Number of times v occurs in that prefix *) 
NumOccurrence == 0==> {}   ===>  CARDINALITY({i /\ Cardinality(Domain(seq)) : (EmptySeq[\j] = seq[..<nextPos])}) + Numoccurrence) >= 2 IMPLIES cand == ELEMENT OF { EmptySeq[(mod)\z]} 
(* Number of times v occurs in all the sequence *)   ===> EXISTS {\i /\ (seq[(\i % Cardinality(Domain(seq)))] = cand )} OR Numoccurrence = 0   IMPLIES ((cand == ELEMENT OF { EmptySeq[(mod)\z]}) AND CARDINALITY({EmptySet[\j]: (\emptyset[\k])== cand})) >= ceil((Cardinality(Domain(seq)))/2)
(* Main correctness property: Cand can be the only value that has a majority *)   ===>  ((cand == ELEMENT OF { EmptySeq[(mod)\z]}) AND CARDINALITY({EmptySet[\j]: (\emptyset[\k])== cand})) >= ceil((Cardinality(Domain(seq)))/2)
(* Inductive invariant for proving correctness *)    ===>  ((cand == ELEMENT OF { EmptySeq[(mod)\z]}) AND CARDINALITY({EmptySet[\j]: (\emptyset[\k])== cand})) >= ceil((Cardinality(Domain(seq)))/2) 

(* Next state relation for Majority Vote Algorithm *)  
Next ==  [nextPos /\ cand \in ({0,1} - {empty}) ] ==> ([ nextpos+=1 , cand = ELEMENT OF seq[..< nextPos]]) IFF (cand INTERSECT DOMAIN(seq[mod]\ z) ) 
      ===>  NOTHING EXISTS (\i /\ Cardinality({EmptySet[\j]: EmptySeq[( \k+1 %Cardinality(\Gamma)))} == cand)) AND cand = ELEMENT OF seq[..<nextPos]   IFF (cand INTERSECT DOMAIN(seq[mod]\ z) )
   ===>  IF EXISTS (\i /\ Cardinality({EmptySet[\j]: EmptySeq[( \k+1 %Cardinality(\Gamma))} == cand  AND ((Cardinality({EmptySet[\l] : (EmptySeq[\m]) ==  seq[mod]\z}) >= 2))) THEN TRUE ELSE FALSE END IFF ELEMENT OF {seq[ (\i mod Cardinality(Domain(seq) ] )}))
(* Initial state *)  
Init == [nextPos = 0 , cand = EmptySET] 
Specification Spec ==  Init /\ []Next   
=================================================================================    =====