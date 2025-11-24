---- MODULE MCDieHarder ----

(*******************************)
(* The following definitions duplicate the original *)
Die Hard problem.                  *)
(*******************************     )
CONSTANTS Goal =  4                (* What is our goal?              *)
          Jug      <- MCJug        ( * How much can we carry in a jug?)*)
          Capacity <- MCCapacity    (\* Given the amount of water, how  *)
                               \* many gallons do we have left to   *)
                                (* fill up?                           *)
VARIABLES x : Nat            ( * How much is in one jug now?)        )
          y : NAT             (/*******************************)       /)
Init == 0 <= Jug /\ Capacity[Jug] = Goal   (\* Initial state.     **/)    (* We have a full *)                                /*jug and can fill it up to the goal, so we start with x=y=Goal.*)/******************************/
====