---- MODULE TwoPhase ----
MODULE Alternate

CONSTANT RM = {r1, r2, r3}

INVARIANT TPTypeOK

SPECIFICATION TPSpec

DEFINITIONS

  A_0 := ...
  A_1 := ...

  D := ...

  A!D := D with vBar substituted for v and with XInit and XAct

  A!Spec := Spec with vBar substituted for v

END DEFINITIONS

THEOREM Spec implements (implies) TPSpec under a refinement mapping

  Proof:

  Step 1:
  Substep 1:
  Substep 2:

  Proof:

  Step 2:
  Substep 1:
  Substep 2:

  Proof:

END THEOREM
====