---- MODULE Majority ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

(***************************************************************************)
(* Definitions used for stating correctness.                                 *)
(***************************************************************************)
CONSTANTS   MaxLen == \* The maximum length of the sequence to be checked by TLC.
                   10^6    (* You can change this value according to your needs. *) 
VARIABLES   seq,        cand,       lbnd,         j == 0..MaxLen -> Nat
            prefixCount == [j ../ (cand = v)] : j .. MaxLen -> 2 * FiniteSet(seq[j])]
            == {v |-> Count(({i | 1 <= i < j} & seq) , v)}   (* Number of times v occurs in the prefix strictly before position j *) 
            totalCount == [0 .. MaxLen -> 2 * FiniteSet(seq[j])] : (cand = v)] : j .. MaxLen -> Nat ]
            == {v |-> Count(({i | 1 <= i < MaxLen} & seq) , v)} (* Number of times v occurs in the sequence *) 
=============================================================================
(* Inductive invariant for proving correctness.                             *)
INVARIANT MajorityInv == (lbnd + totalCount[cand] > Cardinality(seq)/2 ) /\  
                          ((j = MaxLen) => lbnd >= totalCount[cand])  (* The candidate has a majority if its lower bound is greater than or equal to half the sequence length. *) 
=============================================================================
(* Main correctness property: cand can be the only value that has a majority.*)
PROPERTY MajorityProp == (lbnd + totalCount[cand] > Cardinality(seq)/2 ) /\   (* The candidate has a majority if its lower bound is greater than or equal to half the sequence length *) 
                          ((j = MaxLen) => lbnd >= totalCount[cand])         (* and it holds for all positions in the prefix strictly before j.*) 
=============================================================================
(* TLC Configuration:                                                       *)
CONSTANTS   Len == Cardinality(seq), Cand == 0..MaxLen -> Nat, Lbnd == 0..Cardinality(seq)/2 -> 1 + FiniteSet(({i | 1 <= i < MaxLen} & seq) , v))  (* The length of the sequence and initial values for cand and lbnd *)
SPECIFICATION MajorityProp /\ (NOT EXISTS {v |-> Cand[v] = Lbnd})   (* Specify that we want to check both properties, but not just one.*) 
INVARIANT MajorityInv                                                     (* Check the inductive invariant *) 
====                                                                       (* End of specification and proof *)
====