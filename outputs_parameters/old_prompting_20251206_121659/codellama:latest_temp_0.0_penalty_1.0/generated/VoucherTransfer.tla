---- MODULE VoucherTransfer ----
EXTENDS VoucherLifeCycle
CONSTANTS
  V = {v1, v2, v3}
  SH = {src1, src2, src3}
  DH = {dst1, dst2, dst3}
VARIABLES
  vtpState : {Initial, Prepared, Transfer, Abort}
  shState : {Initial, Prepared, Transfer, Abort}
  dhState : {Initial, Prepared, Transfer, Abort}
  vtpTPrepared : {v | v \in V}
  shTPrepared : {v | v \in V}
  dhTPrepared : {v | v \in V}
INIT
  vtpState = Initial
  shState = Initial
  dhState = Initial
  vtpTPrepared = {}
  shTPrepared = {}
  dhTPrepared = {}
NEXT
  vtpState ==
    IF vtpState = Initial
    THEN
      IF shState = Prepared /\ dhState = Prepared
      THEN Prepared
      ELSE IF shState = Transfer /\ dhState = Transfer
      THEN Transfer
      ELSE IF shState = Abort /\ dhState = Abort
      THEN Abort
      ELSE Initial
    ELSE IF vtpState = Prepared
    THEN
      IF shState = Transfer /\ dhState = Transfer
      THEN Transfer
      ELSE IF shState = Abort /\ dhState = Abort
      THEN Abort
      ELSE Prepared
    ELSE IF vtpState = Transfer
    THEN
      IF shState = Abort /\ dhState = Abort
      THEN Abort
      ELSE Transfer
    ELSE IF vtpState = Abort
    THEN Abort
  shState ==
    IF shState = Initial
    THEN
      IF vtpState = Prepared /\ v \in vtpTPrepared
      THEN Prepared
      ELSE Initial
    ELSE IF shState = Prepared
    THEN
      IF vtpState = Transfer /\ v \in vtpTPrepared
      THEN Transfer
      ELSE IF vtpState = Abort /\ v \in vtpTPrepared
      THEN Abort
      ELSE Prepared
    ELSE IF shState = Transfer
    THEN
      IF vtpState = Abort /\ v \in vtpTPrepared
      THEN Abort
      ELSE Transfer
    ELSE IF shState = Abort
    THEN Abort
  dhState ==
    IF dhState = Initial
    THEN
      IF vtpState = Prepared /\ v \in vtpTPrepared
      THEN Prepared
      ELSE Initial
    ELSE IF dhState = Prepared
    THEN
      IF vtpState = Transfer /\ v \in vtpTPrepared
      THEN Transfer
      ELSE IF vtpState = Abort /\ v \in vtpTPrepared
      THEN Abort
      ELSE Prepared
    ELSE IF dhState = Transfer
    THEN
      IF vtpState = Abort /\ v \in vtpTPrepared
      THEN Abort
      ELSE Transfer
    ELSE IF dhState = Abort
    THEN Abort
  vtpTPrepared ==
    IF vtpState = Prepared
    THEN vtpTPrepared \union {v}
    ELSE vtpTPrepared
  shTPrepared ==
    IF shState = Prepared
    THEN shTPrepared \union {v}
    ELSE shTPrepared
  dhTPrepared ==
    IF dhState = Prepared
    THEN dhTPrepared \union {v}
    ELSE dhTPrepared
PREDICATE VTPTypeOK
  IF vtpState = Initial
  THEN TRUE
  ELSE IF vtpState = Prepared
  THEN vtpTPrepared \subseteq V
  ELSE IF vtpState = Transfer
  THEN vtpTPrepared \subseteq V
  ELSE IF vtpState = Abort
  THEN vtpTPrepared \subseteq V
  ELSE FALSE
PREDICATE VTPConsistent
  IF vtpState = Initial
  THEN TRUE
  ELSE IF vtpState = Prepared
  THEN shTPrepared \subseteq V /\ dhTPrepared \subseteq V
  ELSE IF vtpState = Transfer
  THEN shTPrepared \subseteq V /\ dhTPrepared \subseteq V
  ELSE IF vtpState = Abort
  THEN shTPrepared \subseteq V /\ dhTPrepared \subseteq V
  ELSE FALSE
PREDICATE VTPSpec
  IF vtpState = Initial
  THEN TRUE
  ELSE IF vtpState = Prepared
  THEN shState = Prepared /\ dhState = Prepared
  ELSE IF vtpState = Transfer
  THEN shState = Transfer /\ dhState = Transfer
  ELSE IF vtpState = Abort
  THEN shState = Abort /\ dhState = Abort
  ELSE FALSE
\* Refinement does not hold
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
\* Refinement does not hold
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
====