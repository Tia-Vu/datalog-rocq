From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From Datalog Require Import FancyNotations.
From Stdlib Require Import List.
Import ListNotations.
Open Scope string_scope.

Definition rel := string.
Definition fn := string.
Definition var := string.
Definition aggregator := string.

Definition fact := fact rel var fn.
Definition expr := expr var fn.
Definition rule := rule rel var fn aggregator.

Definition empty_rule : rule :=
  {| rule_agg := None; 
     rule_hyps := [];
     rule_concls := [] |}.

Definition edge_path_rule : rule :=
  {| rule_agg := None;
     rule_hyps := [
      {| fact_R := "edge";
         fact_args := [(var_expr "x"); (var_expr "y")]|}
     ]; 
     rule_concls := [
       {| fact_R := "path";
         fact_args := [(var_expr "x"); (var_expr "y")]|}
     ] |}.

(* Constants *)

(* Helper to create a constant (as a nullary function) *)
Definition const (c : fn) : expr := fun_expr c [].

(* Example: edge(x, 42) :- node(x) 
   This represents "for all x, if x is a node, then there's an edge from x to node 42" *)
Definition everything_connects_to_42_rule : rule :=
  {| rule_agg := None;
     rule_hyps := [
      {| fact_R := "node";
         fact_args := [var_expr "x"] |}
     ];
     rule_concls := [
       {| fact_R := "edge";
          fact_args := [var_expr "x"; const "42"] |}
     ] |}.

(* Example: friends(alice, bob) :- . 
   A fact about friendship with only constants *)
Definition alice_bob_friend : rule :=
  {| rule_agg := None;
     rule_hyps := [];
     rule_concls := [
       {| fact_R := "friends";
          fact_args := [const "alice"; const "bob"] |}
     ] |}.