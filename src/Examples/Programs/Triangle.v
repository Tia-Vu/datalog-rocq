(* Auto-generated from SouffleExamples/triangle.dl by souffle_to_rocq *)
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
(* .decl  R(x:number{->Z}, y:number{->Z}) *)
(* .decl  S(y:number{->Z}, z:number{->Z}) *)
(* .decl  T(z:number{->Z}, x:number{->Z}) *)
(* .decl  Triangle(x:number{->Z}, y:number{->Z}, z:number{->Z}) *)

(* Triangle(x, y, z) :- R(x, y), S(y, z), T(z, x). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "Triangle"; clause.args := [(expr.var "x"); (expr.var "y"); (expr.var "z")] |}
    ]) ([
      {| clause.rel := "R"; clause.args := [(expr.var "x"); (expr.var "y")] |};
      {| clause.rel := "S"; clause.args := [(expr.var "y"); (expr.var "z")] |};
      {| clause.rel := "T"; clause.args := [(expr.var "z"); (expr.var "x")] |}
    ]).

Definition program : list rule :=
  [rule_0].

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
        rule_0.

Compute get_program_dependencies_flat computed_program.