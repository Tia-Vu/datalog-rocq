From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.
#[local] Instance string_fn : fnT := string.

Definition empty_rule : rule := rule.impl [] [].

Definition edge_path_rule : rule :=
  rule.impl
    [ {| clause.rel := "path"; clause.args := [expr.var "x"; expr.var "y"] |} ]
    [ {| clause.rel := "edge"; clause.args := [expr.var "x"; expr.var "y"] |} ].

(* Constants *)

(* Helper to create a constant (as a nullary function) *)
Definition const (c : string) : expr := expr.app c [].

(* Example: edge(x, 42) :- node(x)
   This represents "for all x, if x is a node, then there's an edge from x to node 42" *)
Definition everything_connects_to_42_rule : rule :=
  rule.impl
    [ {| clause.rel := "edge"; clause.args := [expr.var "x"; const "42"] |} ]
    [ {| clause.rel := "node"; clause.args := [expr.var "x"] |} ].

(* Example: friends(alice, bob) :- .
   A fact about friendship with only constants *)
Definition alice_bob_friend : rule :=
  rule.impl
    [ {| clause.rel := "friends"; clause.args := [const "alice"; const "bob"] |} ]
    [].

Definition basic_program: list rule :=
   [edge_path_rule; everything_connects_to_42_rule; alice_bob_friend].

Definition computed_basic_program := Eval compute in basic_program.
Print computed_basic_program.
