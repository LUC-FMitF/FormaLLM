---- MODULE Relation ----

(***********************************************************************
* This module provides some basic operations on relations, represented *
as binary Boolean functions over some set S.                          *)
(* Modification History: Last modified Sun Jun 14 15:32:47 CEST 2020   *)
(by merz) Created Tue Apr 26 10:24:07 CEST 2016 by merz                      )
***************************************************************************)
CONSTANTS S, R \* The set and relation to operate on. *\/
VARIABLES x, y   \* Temporary variables for operations.       *)
------------------------------ Axioms ----------------------------
Reflexive == /\ (\A s:s \in S |-> (R[x=y] = TRUE))     (* Is the relation R reflexive over set S?                                *)
Irrefl    ==  /\\ x, y : ~(x=y) => !((R)[x=y])         *\/ Irreflextivity. The negation of a statement is always false.          \*)
Symmetric == /\ (\A s:s \in S |-> (~!(![x] = [y]))     (* Is the relation R symmetric over set S?                                *)
Asymm      ==  /\\ x, y : !([x=y]) => ~(R)[x=y]        *\/ Asymmetry. The negation of a statement is always false.               \*)
Transitive == /\ (\A s:s1 \in S |-> (~!(![x][y]))      (* Is the relation R transitive over set S?                    *)
Tran       ==  /\\ x, y : !([z] => ~!(R)[x=z])   *\/ Transitivity. The negation of a statement is always false.*\*)
------------------------------ Definitions --------------------------
TransClosure(r) =                                (* Compute the transitive closure of relation R over set S.) *)
  /\ (\A s:s \in S |-> (~!(![x][y] => ~!(R)[z=u]))   *\/ Transitivity. The negation of a statement is always false.*\*)
ReflexiveTransClosure(r) =                        (* Compute the reflexive transitive closure of relation R over set S.) *)
  /\ (\A s:s \in S |-> (~!(![x][y] => ~!(R)[z=u]))   *\/ Transitivity. The negation of a statement is always false.*\*)
------------------------------ Axioms ----------------------------
Connected ==                                (* Is the relation R connected over set S, i.e. does there exist  *)
    /\ (\A s:s1 \in S |-> (~!(![x][y] => ~!(R)[z=u]))   *\/ Transitivity. The negation of a statement is always false.*\*)
                       && /\\ x, y : !([x]= [y])  (* A path between two arbitrary elements exists? *)               \*/ PathExistence*\)
====