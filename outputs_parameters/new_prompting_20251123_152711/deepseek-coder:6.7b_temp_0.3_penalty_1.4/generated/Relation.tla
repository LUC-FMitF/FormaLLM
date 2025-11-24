---- MODULE Relation -----

(*************************************************************************************
This module provides some basic operations on relations, represented as binary Boolean *)
(* functions over some set S.                                                        *)
*************************************************************************************)

CONSTANTS   SetS \* The set of all elements in the universe;
VARIABLES   RelR  \* A relation R between two sets from S to S.
--------------------------------------------------------------------------------------
Reflexive(Rel,Set) == EXISTS x : (x , x ) ElemOf Domain[InvImage[Range - Range](Rel)] *) (* Is the relation Refl over set Set?*)
Irreflexive(Rel,Set)== NOT [EXISTS x: (x,y)\in Rel] FORALL y\in Set  \*Is the relation Irrefl over set S?*)
Symmetric(Rel,Set)  == EXISTS {X , Y} : (( X ,Y ) IN Rel ==> ( Y ,X )IN Rel ] *) (* Is the relation Symm over set S?*)
Asymmetric(Rel,Set) ==  NOT [EXISTS x:((x,y)\in Rel AND  ( y ,x ) \in Rel)] FORALL {x,y} : ((x,y)\in Rel))   \*Is the relation Asymm over set S?*)
Transitive(Rel,Set) == EXISTS {{X1,Y1},{X2,Y2}}:(( X1 , Y1 ) IN Rel AND ( Y1 , Y2 )\IN Rel==>({X1,Y2}\in Rel)) *) (* Is the relation Trans over set S?*)
TransClosure(Rel) == UNION {Powerset[Range](Rel),{EXISTS {{x,y},{y,z}}:(( x , y )\IN Rel AND ( y , z ) \IN Rel==>({x,z}\in Rel)) }} *) (* Compute the transitive closure of relation R over set S.*)
ReflTransClosure(Rel) == UNION {Powerset[Range](Rel),{EXISTS {{x,y},{y,z}}:(( x , y )\IN (Rel \ Union Range[(InvImage - InvImage)[Domain - Domain[Set]](Rel)] ) AND (( y , z ) IN Rel OR( z , y) IN Rel)) }} *) (* Compute the reflexive transitive closure of relation R over set S.*)
Connected(Rel, SetS) == NOT EXISTS {{x1, x2}: (x1 \in Domain[Set] /\  x2 \in Range[(InvImage - InvImage)[Domain - Domain[Set]](Rel)])} : ((x1 , x2)\IN Rel OR (x2 , x1) IN Rel)) *) (* Is the relation R connected over set S, i.e., does there exist a path between two arbitrary elements of SetS?*)
Spec == [Connected(ReflTransClosure[RelR],SetS)]\/\/[][(Asymmetric[RelR,SetS])\/\/(Irreflexive[RelR,SetS])]\/\/[][(Transitive[RelR,SetS) \/\/(Symmetric[RelR,SetS]))\]
=======================================================================================
====  CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); (* TLC Configuration *)
     SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================
====  (* TLC Configuration *)
     CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================
====  (* TLC Configuration *)
     CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================
====  (* TLC Configuration *)
     CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================
====  (* TLC Configuration *)
     CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================
====  (* TLC Configuration *)
     CONSTANTS SetS = {1 ,2 ,3 } ; RelR(x,y): ( x =  y ) OR ( x +  2 * y < 6 ); SPECIFICATION Spec; INVARIANTS [Connected[ReflTransClosure[RelR],SetS),[][(Asymmetric[RelR,SetS) \/\/(Irreflexive[RelR,SetS]))]\/\/[][(Transitive[RelR,SetS)) \/\/(Symmetric[RelR,SetS])]];
=======================================================================================.
====