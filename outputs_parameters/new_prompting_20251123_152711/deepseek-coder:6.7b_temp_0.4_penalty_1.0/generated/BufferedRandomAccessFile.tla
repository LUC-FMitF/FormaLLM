---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                        *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and      *)
(* setLength operations.                                                     *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
CONSTANT Symbols = {A, B}  (* data stored in the file (in reality there are 256 symbols: bytes 0x00 to 0xFF) *)
CONSTANT ArbitrarySymbol = `ArbitrarySymbol'  (* special token for an arbitrary symbol *)
CONSTANT MaxOffset = MAXINT - 1  (* highest possible offset (in reality this is 2^63 - 1) *)
CONSTANT BuffSz = 2  (* buffer size, used in the write and read operations *)
  
VARIABLE lo : [0 .. MaxOffset]  (* lower bound for seeking *)
VARIABLE hi : [lo + 1 .. MAXINT]  (* upper bound for seeking *)
VARIABLE fp : [lo - BuffSz/2, ... , hi + BuffSz/2]  (* file pointer position within the bounds defined by lo and hi *)
  
\* Internal invariants (copied from comment in BufferedRandomAccessFile.java) \*/
INVARIANT Inv1 == fp >= lo - BuffSz / 2 AND fp <= hi + BuffSz / 2 (* ... *)
INVARIANT Inv2 == 0 (* see note at definition of Inv2 *)
(*... other invariants ...*)
  
\* Properties (refinements) for the operations *\)
PROPERTY FlushBufferCorrect == \*...*\
PROPERTY SeekCorrect == fp' >= lo AND fp <= hi (* see note at definition of Inv2 *)
(*... other properties ...*)
  
\* Operations on file data (read, write) *\)
OPERATION Read1(n : NATURAL) RETURNS [0 .. n] -> BOOLEAN == \*...*\
OPERATION Write1Correct(data_to_write: [0..256]) RETURNS VOID ==  (* general contract of the file `write()` call *)
(*... other operations ...*)
  
\* Specification *\)
SPECIFICATION Spec == \*...*\

=============================================================================
====