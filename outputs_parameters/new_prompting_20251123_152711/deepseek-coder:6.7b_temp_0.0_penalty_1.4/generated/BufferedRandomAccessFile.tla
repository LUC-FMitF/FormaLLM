---- MODULE BufferedRandomAccessFile 
------------------------------ MODULE BufferedRandomAccessFile ----------------------------
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates. *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and *)
(* setLength operations. *)
(***************************************************************************)

EXTENDS RandomAccessFile

CONSTANTS 
    Symbols = {A, B} (* data stored in the file (in reality there are 256 symbols: bytes 0x00 to 0xFF) *)
    ArbitrarySymbol = ArbitrarySymbol (* special token for an arbitrary symbol (to reduce the need for nondeterministic choice) *)
    MaxOffset = 3 (* the highest possible offset (in reality this is 2^63 - 1) *)
    BuffSz = 2 (* The set of legal offsets *)
    
VARIABLES 
    file << Symbols >> (* the underlying file *)
    lo, hi INTEGER1 (* in-memory variables (BufferedRandomAccessFile class fields) *)
    dirty BOOLEAN (* Internal invariants (copied from comment in BufferedRandomAccessFile.java) *)
    Inv2 BOOLEAN (* denoted c(f) in .java file, denoted disk(f)[i] in .java file *)
    
Init == <...> (* Initial state predicate - to be defined *)
Next == <...> (* Next-state relation - to be defined *)
Spec == Init /\ [][Next]_<<file>> (* Specification - to be defined *)

(* Helper definitions for model checking *)
Symmetry == (lo, hi) = (hi, lo) (* Symmetry property *)
Alias == file' = file (* Aliasing property *)
Inv2CanAlwaysBeRestored == ~dirty => Inv2 (* Property ensuring that Inv2 can always be restored *)
(* More helper definitions for model checking - to be defined *)

====