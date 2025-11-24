---- MODULE MCEWD687a --------------------------------------------------------------
-------------------------------------------------------------------------------
(*****************************************************************************)
(*                                                                            *)
(*    This module defines a distributed algorithm for maintaining a BST.     *)
(*                                                                            *)
(*                                                                            *)
(*  Copyright (c) 2016-2021, Microsoft Research, Daan Leijen and Tommi Jaakkola.   *)
(*                                                                            *)
(*  This program is free software: you can redistribute it and/or modify     *)
(*  it under the terms of the GNU General Public License as published by     *)
(*  the Free Software Foundation, either version 2 of the License, or        *)
(*  any later version.                                                       *)
(*                                                                            *)
(*  This program is distributed in the hope that it will be useful,          *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of           *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the            *)
(*  GNU General Public License for more details.                             *)
(*                                                                            *)
(*  You should have received a copy of the GNU General Public License        *)
(*  along with this program. If not, see <http://www.gnu.org/licenses/>.    *)
(*                                                                            *)
(******************************************************************************)

CONSTANT L = 3
CONSTANT P1 = 1
CONSTANT P2 = 2
CONSTANT P3 = 3

MV CONSTANT definitions @modelParameterConstants:1Edges
MV CONSTANT definitions @modelParameterConstants:2Leader

CONSTANT
    Procs <- const_1633116534008310000
\* CONSTANT definitions

CONSTANT
    Edges <- const_1633116534008311000
\* CONSTANT definitions

CONSTANT
    Leader <- const_1633116534008312000

\* CONSTRAINT definition
CONSTRAINT
    constr_1633116534008313000

\* SPECIFICATION definition
SPECIFICATION
    Spec

CHECK_DEADLOCK
    FALSE

\* INVARIANT definition
INVARIANT
    TypeOK
    DT1Inv

\* PROPERTY definition
PROPERTY
    DT2

PROPERTIES  
    CountersConsistent
    TreeWithRoot
    \* StableUpEdge

\* Generated on Fri Oct 01 12:28:54 PDT 2021
====