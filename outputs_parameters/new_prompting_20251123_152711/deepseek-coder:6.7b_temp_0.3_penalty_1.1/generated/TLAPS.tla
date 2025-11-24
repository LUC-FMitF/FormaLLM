---- MODULE TLAPS ----
-- Module Definition
MODULE Example
EXTENDS Naturals
CONSTANT MaxSize = 10;
VARIABLE Buffer : {<0,MaxSize>};
ASSUME Initially Buffer = {} AND Length(Buffer) <= MaxSize;

DEFINE
  -- Add an element to the buffer
  add == \x => IFLEN(Buffer) < MaxSize THEN {Buffer} UNION {x} ELSE Buffer;

  -- Remove an element from the buffer
  remove == \ => IF #Buffer > 0 THEN {<Buffer - {Choose X in Buffer}>} ELSE Buffer;

  -- The specification
  spec == ASSUME Length(Buffer) <= MaxSize /\ EVENTUALLY (Length(Buffer) = 0);
ENDDEFINE
====