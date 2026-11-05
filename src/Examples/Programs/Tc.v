(* Auto-generated from SouffleExamples/tc.dl by souffle_to_rocq *)
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
(* .decl  tcl(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tcr(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  base(node1:number{->Z}, node2:number{->Z}) *)
(* .decl  tc(node1:number{->Z}, node2:number{->Z}) *)

(* tcl(X, Y) :- base(X, Y). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "tcl"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "base"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]).

(* tcl(X, Y) :- tcl(X, Z), base(Z, Y). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "tcl"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "tcl"; clause.args := [(expr.var "X"); (expr.var "Z")] |};
      {| clause.rel := "base"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Y). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "tcr"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "base"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]).

(* tcr(X, Y) :- base(X, Z), tcr(Z, Y). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "tcr"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "base"; clause.args := [(expr.var "X"); (expr.var "Z")] |};
      {| clause.rel := "tcr"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

(* tc(X, Y) :- base(X, Y). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "tc"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "base"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]).

(* tc(X, Y) :- tc(X, Z), tc(Z, Y). *)
Definition rule_5 : rule :=
rule.impl ([
      {| clause.rel := "tc"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "tc"; clause.args := [(expr.var "X"); (expr.var "Z")] |};
      {| clause.rel := "tc"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4;
   rule_5].

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