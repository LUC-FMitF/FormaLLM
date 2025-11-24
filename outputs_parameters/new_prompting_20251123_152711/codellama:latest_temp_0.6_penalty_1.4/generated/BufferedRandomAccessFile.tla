---- MODULE BufferedRandomAccessFile ----
(**********************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates. *)
(* This is a model-checkable specification for Buffer*)
(* RandomAccessFile.java. It covers the core fields as well as the seek, read, write, flush, and setLength operations.*)
(**********************************************)
CONSTANT Symbols = {A, B}
CONSTANT ArbitrarySymbol = ArbitrarySymbol
CONSTANT MaxOffset = 3
CONSTANT BuffSz = 2
  
\* Helper for Seek (not a full action): constrains diskPos', file_pointer' and buff'.*)
LOCAL ZSeqFromSeq(seq) == [i \in DOMAIN seq |-> seq[i]]
  
(* Internal invariants *)
INVARIANT Inv1 == /\ f.closed = closed(f) ==> ~ENABLED FlushBuffer  (* close() not described in this spec*)
\* INVARIANT Inv2 == \/ ENABLED Seek(curr) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
INVARIANT Inv3 == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* INVARIANT Inv4 == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
INVARIANT Inv5 == /\ f.closed = closed(f) ==> ~ENABLED Read  (* close() not described in this spec*)
\* INVARIANT Inv6 == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
  
PROPERTY Safety == /\ f.closed = closed(f) ==> ~ENABLED Seek  (* close() not described in this spec*)
\* PROPERTY FlushBufferCorrect == \/ ENABLED FlushBuffer --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY SeekCorrect == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY Write1Correct == \/ ENABLED Write(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY Read1Correct == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY WriteAtMostCorrect == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY ReadCorrect == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY SeekEstablishesInv2 == \/ ENABLED Seek(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
  
SYMMETRY Symmetry == /\ f.closed = closed(f), g.closed = closed(g) ==> (SymmetricBufferedRandomAccessFile(f, g)) <-> (SymmetricBufferedRandomAccessFile(g, f))  (* symmetry of the spec*)
ALIAS Alias == \/ ENABLED Write(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
  
\* Helper for Seek (not a full action): constrains diskPos', file_pointer' and buff'.*)
LOCAL ZSeqFromSeq(seq) == [i \in DOMAIN seq |-> seq[i]]
  
(* Internal invariants *)
INVARIANT Inv1 == /\ f.closed = closed(f) ==> ~ENABLED FlushBuffer  (* close() not described in this spec*)
\* INVARIANT Inv2 == \/ ENABLED Seek(curr) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
INVARIANT Inv3 == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* INVARIANT Inv4 == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
INVARIANT Inv5 == /\ f.closed = closed(f) ==> ~ENABLED Read  (* close() not described in this spec*)
\* INVARIANT Inv6 == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
  
PROPERTY Safety == /\ f.closed = closed(f) ==> ~ENABLED Seek  (* close() not described in this spec*)
\* PROPERTY FlushBufferCorrect == \/ ENABLED FlushBuffer --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY SeekCorrect == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY Write1Correct == \/ ENABLED Write(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY Read1Correct == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY WriteAtMostCorrect == \/ ENABLED WriteAtMost(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
PROPERTY ReadCorrect == /\ f.closed = closed(f) ==> ~ENABLED SetLength  (* close() not described in this spec*)
\* PROPERTY SeekEstablishesInv2 == \/ ENABLED Seek(_) --> RestoreInv2(* by definition; see `file_pointer <- curr` in refinement mapping below.*)
====