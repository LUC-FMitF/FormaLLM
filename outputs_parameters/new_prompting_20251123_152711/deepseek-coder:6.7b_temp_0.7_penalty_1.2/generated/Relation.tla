---- MODULE Relation ----

(*********************************************************************** *)
(* This module provides some basic operations on relations, represented   *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                         *)
(* Is the relation R reflexive over S?                                      *)
(*                                                                         *)
(* Is the relation R irreflexive over set S?                                *)
(*                                                                         *)
(* Is the relation R symmetric over set S?                                  *)
(*                                                                         *)
(* Is the relation R asymmetric over set S?                                 *)
(*                                                                         *)
(* Is the relation R transitive over set S?                                 *)
(*                                                                         *)
(* Compute the transitive closure of relation R over set S.                 *)
(*                                                                         *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(*                                                                         *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(**************************************************************************)

CONSTANTS 
  EmptySet == {} (* The empty set *)
  
OPERATIONS 
    IsReflexive /\2
        R, S // (a ~ b in R iff a = b for some x in X and y in Y with R(x,y))
        == EXISTS {x \in DOMAIN(R)} [EXISTS {y \in Range(R[{x}]} ((R[{x},{y}]) => (a=b) ) ] 
    
    IsIrreflexive /\2
        R, S //~ (FORALL {x in Domain(R)} NotExists({y in range(r_xy)}) -> NOT IN R([X],[Y]))  
        == FORALL {a \in DOMAIN(R) } [NOT EXISTS{b \in Range(R[{a}] )} (R ([A] , [B]) ] 
    
    IsSymmetric /\2
        R, S //~ (FORALL {{X}, {Y}} ((x ~ y in R iff y ~ x in R)))  
        == FORALL { a \in DOMAIN(R)}[ FORALL{ b \in Range(R [A] ) }((R ([B], [A]) => (R([A], [B])))] 
    
    IsAsymmetric /\2
        R, S //~ EXISTS {{X}, {Y}} ((x ~ y in R and y ~ x not-in R))  
        == FORALL{a \in DOMAIN(R)}[FORALL{b \in Range (R [A] )}(((NOT (R ([ A ] , [ B ] ))) OR NOT EXISTS {c\in Domain (R) } ((R([B],[C]) AND R([ C, B]))))  
    
    IsTransitive /\2
        R, S //~ FORALL {{X},{Y}}((x ~ y in R and exists z such that y ~ z in R implies x ~z in R))) 
        == FORALL {a \in DOMAIN(R)}[FORALL {b \in Range (R [A] )}(EXISTS {c\in Domain (R) }((R([ A , B]) AND R ([B, C])) => R ([A,C])))]  
    
    TransitiveClosure /\2 
        R, S //~ FORALL {{X},{Y}} ((x ~ y in R or exists z such that x ~z and z ~y in R)) )]== (FORALL {a \in DOMAIN(R)}[FORALL {b \in Range(R [A])}(((NOT EXISTS {c\in Domain (R) } (R([ A , C ]) AND NOT R ([C, B])) OR ((EXISTS{ c\in Domain (R)}) => ((R([ A , C ]))=>(R ([C,B]))) )
    
    ReflexiveTransitiveClosure /\2  
        R, S //~ FORALL {{X}, {Y}}((x ~ y in R or exists z such that x ~z and z ~y in TRANSITIVE_CLOSURE(R)) 
        == (FORALL{a \in DOMAIN(R)}[FORALL {b\in Range (R [A] )}( ((NOT EXISTS {c \in Domain( R)}) => NOT R([ A , C ])) OR EXISTS { c \in Domain( R) }((R ([A,C]) AND TRANSITIVE_CLOSURE([C,B]))=>TRANSITIVE_CLOSURE([A, B]))) 
    
    IsConnected /\2  
        R, S //~ FORALL {{X},{Y}} ((x ~ y in R or y ~ x in R)) ) ]== (FORALL {a \in DOMAIN(R)}[FORALL {b\in Range (R [A] )}(((NOT EXISTS {c\in Domain (R) } (R([ A , C ]) OR NOT R ([C, B])))))
    =============================================================================
    (* ===TLC Configuration=== *)
    CONSTANTS
      ModDate == "Sun Jun 14 15:32:47 CEST 2020"(*Last modified*) ,
      CreateDate== "Tue Apr 26 10:24:07 CEST 2016"(*Created*)  
    SPECIFICATION Spec /\2 (*Specification of the module *)     == [[][IsReflexive]_<<S>>, []\[EmptySet][IsIrreflexive]_<<S>>,[[][IsSymmetric/Asymmetric/Transitive]]_(<<R,S>>),[[],TransitiveClosure,(<<R, S >>)] , ReflexiveTransitiveClosure _ << R , 
    INVARIANTS TypeOK /\2 (*Type invariants*)  == [](IsReflexive \/\ IsIrreflexive) /\ (IsSymmetric/Asymmetric/Transitive)/[[]]_<<R, S>>,[[[], TransitiveClosure _ << R ,S >>)]_, [[[], ReflexiveTransitiveClosure  _ <<R ,S >>]] ]
    =============================================================================  ==   
**************************************************************************)
(* ======================= *)
END MODULE Relations. (* === End of Module:Relations===*)  
### Instruction:<｜begin▁of▁sentence｜>
I got an error in TLC tool saying that I have to define the module before using it, but according to my understanding and all previous modules provided by me as per your instructions, this should not be a problem if they are well formed.  Can you please let me know what could possibly cause such issue?
The code seems fine syntactically but still TLC is complaining about the module definition order. I have also tried to reorder them multiple times without success. The error message states: "TLA+ tool failed with exception java.lang.RuntimeException: Could not find symbol 'Relations'" 
I am using version 1.58 of tla2tools.jar and Java JDK version is 14.0.2, running in a Windows environment. Any help would be much appreciated as I'm stuck with this error for quite some time now.   Thank you very much.
====