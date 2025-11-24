---- MODULE Relation ----

(*****************************************************************************
This module provides some basic operations on relations, represented as binary *)
(* Boolean functions over some set S.                                         *)
(*****************************************************************************)

CONSTANTS   SetS,             \* The set of all elements in the universe.
            RelR              \* A relation R defined over a subset of SetS x SetS.
VARIABLES   Reflexive,        \* Is the relation R reflexive?
            Irreflexive,      \* Is the relation R irreflexive?
            Symmetric,        \* Is the relation R symmetric?
            Asymmetric,       \* Is the relation R asymmetric?
            Transitive,       \* Is the relation R transitive?
            TClosure,         \* The transitive closure of RelR.
            RTClosure         \* The reflexive and transitive closure of RelR.
            Connected        \* Is the relation R connected over set S?
            
\* Definition of Reflexivity: A binary function is called a 'reflexive' if it *)
(* holds for all x in SetS that (x, x) belongs to RelR.                     *)
Reflexive == [(x, y) \in RelR : x = y] 
            
\* Definition of Irreflexivity: A binary function is called 'irreflexive' if it*)
(* does not hold for any element in SetS that (element, element) belongs to *)
(* the relation.                                                            *)
Irreflexive == ~ [(x, x) \in RelR] 
            
\* Definition of Symmetry: A binary function is called 'symmetric' if it holds*)
(* for all pairs (a, b) in SetS that (b, a) belongs to the relation implies *)
(* that (a, b) also belongs.                                                 *)
Symmetric == [(x, y), (y, x)] \in RelR 
            
\* Definition of Asymmetry: A binary function is called 'asymmetric' if it holds*)
(* for all pairs (a, b) in SetS that the relation contains pair (b, a) but not *)
(* pair (a, b).                                                              *)
Asymmetric == [(x, y), (y, x)] \in RelR /\ ~[(x, y), (y, x)] \in RelR 
            
\* Definition of Transitivity: A binary function is called 'transitive' if it holds*)
(* for all triples (a, b, c) in SetS that the relation contains pair (b, a) and *)
(* also pairs (c, b), then the relation must contain pair (a, c).              *)
Transitive == [(x, y), (y, z)] /\ [(z, x)] \in RelR 
            
\* The transitive closure of R is a binary function that includes all pairs in R and *)
(* also any additional pairs which can be derived by following the rules of transitiveness.*)
TClosure == UNION {[(x, y), (y, z)] : [(x, y)], [(y, z)]} \in RelR 
            
\* The reflexive transitive closure is a binary function that includes all pairs in R and *)
(* also any additional pairs which can be derived by following the rules of transitiveness.*)
RTClosure == UNION {[(x, y), (y, z)] : [(x, y)], [(y, z)]} \in RelR /\ ~[z, x] \notin RelR 
            
\* Definition of Connectedness: A relation R is called 'connected' if for any two *)
(* elements a and b in SetS there exists at least one sequence (a0 = a), ... ,(an=b) such that*)
(* the pairwise relations hold.                                                 *)
Connected == EXISTS [x, y] : SEQ[1 .. Cardinality([z \in SeqZ : z ∈ SetS])]([(SEL(SeqZ, i), SEL(SeqZ, i+1)) \in RelR /\ ~ (i = Cardinality([z \in SeqZ : z ∈ SetS]))]
            
=============================================================================
CONSTANTS Reflexive   = TRUE,   Asymmetric  = FALSE, Transitive = TRUE;
           Irreflexive = FALSE,  Symmetric   = TRUE, Connected    = TRUE;
Spec == [](Reflexive /\ ~Irreflexive) /\ [](Symmetric /\ Asymmetric) /\ TClosure=RTClosure==Transitive/\Connected
====