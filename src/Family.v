From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Datalog Require Import FancyNotations.
From DatalogRocq Require Import DependencyGenerator.
Import ListNotations.
Open Scope string_scope.


Definition const (c : fn) : expr := fun_expr c [].
Definition var (x : var) : expr := var_expr x.

Definition r_parent_anna : rule :=
  {| rule_agg := None;
     rule_hyps := [];
     rule_concls := [
       {| fact_R := "parent"; fact_args := [const "Anna"; const "Bob"] |}
     ] |}.

Definition r_ancestor1 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "parent"; fact_args := [var "x"; var "y"] |}
     ];
     rule_concls := [
       {| fact_R := "ancestor"; fact_args := [var "x"; var "y"] |}
     ] |}.

Definition r_ancestor2 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "parent"; fact_args := [var "x"; var "z"] |};
       {| fact_R := "ancestor"; fact_args := [var "z"; var "y"] |}
     ];
     rule_concls := [
       {| fact_R := "ancestor"; fact_args := [var "x"; var "y"] |}
     ] |}.

Definition r_sibling : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "parent"; fact_args := [var "p"; var "x"] |};
       {| fact_R := "parent"; fact_args := [var "p"; var "y"] |}
     ];
     rule_concls := [
       {| fact_R := "sibling"; fact_args := [var "x"; var "y"] |}
     ] |}.

Definition r_aunt_uncle : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "sibling"; fact_args := [var "x"; var "p"] |};
       {| fact_R := "parent"; fact_args := [var "p"; var "y"] |}
     ];
     rule_concls := [
       {| fact_R := "aunt_uncle"; fact_args := [var "x"; var "y"] |}
     ] |}.

Definition r_cousin : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "parent"; fact_args := [var "px"; var "x"] |};
       {| fact_R := "parent"; fact_args := [var "py"; var "y"] |};
       {| fact_R := "sibling"; fact_args := [var "px"; var "py"] |}
     ];
     rule_concls := [
       {| fact_R := "cousin"; fact_args := [var "x"; var "y"] |}
     ] |}.

Definition r_bob_parent : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "parent"; fact_args := [const "Bob"; var "x"] |}
     ];
     rule_concls := [
       {| fact_R := "parent"; fact_args := [const "Bob"; const "Charlie"] |}
     ] |}.

Definition family_program := 
  [r_parent_anna;
   r_ancestor1;
   r_ancestor2;
   r_sibling;
   r_aunt_uncle;
   r_cousin;
   r_bob_parent].

Compute get_rule_dependencies family_program r_cousin.