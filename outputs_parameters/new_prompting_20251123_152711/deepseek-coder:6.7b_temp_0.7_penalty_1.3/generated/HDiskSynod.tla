---- MODULE HDiskSynod -----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS NotAnInput = \* A constant representing absence of an input.
     CHOOSE x : UNIVERSAL - {"NotAnInput"}
     
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == 
  IF s = EmptyZSeq THEN {} ELSE DOMAIN s
  
\* The length of zero-indexed sequence s
ZLen(s) == 
  IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

(* CONFIGURATION *)
CONSTANTS BKModel =  \* Banker's Algorithm model.
     [bk |-> <<bal, inp>> : bk IN Instances]  (* bankers can have different balances and inputs *)
OPERATOR BalanceUpdate(x) == <x[1], x[2] + 1>  \* Update the balance of a banker.
INVARIANT BKInv ==  -- At most one input at any given time, except when no input is present. 
     /\ !EXISTING bk : (bk.inp = NotAnInput) => @(Instance -> bal = 0)) AND ((@(Instance->bal=0)/#{x: Instance | x[2] \notin {NotAnInput}} = #(Instance)))
     
\* Modification History
OPERATOR HistUpdate == <NewHist, NewMod>  -- Update the history. 
INVARIANT HistInv ==  [bk|-> (bk.bal = 0) => ((@(bk.hist -> bal=0)))]   (* Banker's balance must be zero if no input is present *)
     
====