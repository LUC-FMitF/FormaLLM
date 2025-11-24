---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                     *)
(**************************************************************************)
(**                                                                        *)
(** Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                    *)
(** Created Sat Jan 26 15:23:57 CET 2019 by tthai                          *)
(**/                                                                       *)
(**************************************************************************)

CONSTANTS
  NotAnInput,   \* The special value for an input that is not an input.
  Input,        \* The set of all inputs.
  Output        \* The set of all outputs.

VARIABLES
  bk,           \* The bank account.
  inp,          \* The input.
  out,          \* The output.

----------------------------------------------------------------------------

Init ==
  /\ bk.bal = 0
  /\ bk.inp = NotAnInput
  /\ out = NotAnInput

----------------------------------------------------------------------------

Next ==
  \/
    \* The transition with input.
    [
      bk' = bk,
      inp' = inp,
      out' = NotAnInput
    ] :
      (bk.inp = NotAnInput \/ bk.inp = inp)
      /\ (bk.bal >= 0)
      /\ (inp = Input)
      /\ (out = NotAnInput)

    \* The transition without input.
    [
      bk' = bk,
      inp' = NotAnInput,
      out' = out
    ] :
      (bk.inp = NotAnInput)
      /\ (bk.bal >= 0)
      /\ (inp = NotAnInput)
      /\ (out = Output)

----------------------------------------------------------------------------

Spec ==
  Init /\ [][Next]_<<bk, inp, out>>

=============================================================================
====