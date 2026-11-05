(* Auto-generated from SouffleExamples/x9.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Stdlib Require Import ZArith.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(* Type parameters                                                      *)
(* Souffle relation/variable names are strings; we use string for       *)
(* rel, var, and fn.  aggregator = unit (aggregation not supported).    *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Schema                                                               *)
(* ------------------------------------------------------------------ *)
(* .decl  X(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  Y(node1:number{->Z}, node2:number{->Z}) *)

(* Y(a, b) :- X(a, b). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "Y"; clause.args := [(expr.var "a"); (expr.var "b")] |}
    ]) ([
      {| clause.rel := "X"; clause.args := [(expr.var "a"); (expr.var "b")] |}
    ]).

(* Y(a, c) :- Y(a, b), Y(b, c). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "Y"; clause.args := [(expr.var "a"); (expr.var "c")] |}
    ]) ([
      {| clause.rel := "Y"; clause.args := [(expr.var "a"); (expr.var "b")] |};
      {| clause.rel := "Y"; clause.args := [(expr.var "b"); (expr.var "c")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1].

Definition computed_program := Eval compute in program.
Print computed_program.


(* Temp fix, may use typeclasses later *)
Definition get_program_dependencies (p : list rule) :=
  DependencyGenerator.get_program_dependencies (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (expr_compatible := expr_compatible)
    p.

Compute get_program_dependencies computed_program.
Compute get_rule_dependencies
        computed_program
        rule_1.

Compute get_program_dependencies_flat computed_program.