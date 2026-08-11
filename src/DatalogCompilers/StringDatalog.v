(* StringDatalog: the *datalog* backend for the compiler -- the program types (relations,
   variables, functions, ... are strings, from StringDatalogParams) together with the sorted-list
   map instances they need.  This is entirely independent of the topology (node ids / graph):
   combine it with a topology backend (e.g. GridTopology) to get a concrete compiler. *)

From DatalogRocq Require Import DistributedDatalogToHardwareCompiler StringDatalogParams.
From coqutil Require Import Map.Interface Map.SortedListString Eqb Decidable.
From GraphSearch Require Import GraphInterface GraphImpl.
Import StringDatalogParams.

(* Variables and functions are strings; string-keyed sorted-list maps resolve for all of them. *)
Existing Instance SortedListString.map.
Existing Instance SortedListString.ok.


