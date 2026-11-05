(* Auto-generated from SouffleExamples/cspa.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* {0: (2, 2), 1: (0, 1), 2: (0, 2), 3: (1, 0), 4: (1, 2), 5: (2, 1), 6: (1, 1), 7: (2, 0), 8: (0, 0), 9: (1, 1)} *)

(* ------------------------------------------------------------------ *)
(* Type parameters                                                      *)
(* Souffle relation/variable names are strings; we use string for       *)
(* rel, var, and fn.  aggregator = unit (aggregation not supported).    *)
(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(* Schema                                                               *)
(* ------------------------------------------------------------------ *)
(* .decl  assign(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  dereference(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  valueFlow(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  valueAlias(x:symbol{->string}, y:symbol{->string}) *)
(* .decl  memoryAlias(x:symbol{->string}, y:symbol{->string}) *)
(* .input  assign *)
(* .input  dereference *)
(* .output valueFlow *)
(* .output valueAlias *)
(* .output memoryAlias *)

(* valueFlow(Y, X) :- assign(Y, X). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "Y"); (expr.var "X")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "Y"); (expr.var "X")] |}
    ]).

(* valueFlow(X, X) :- assign(X, Y). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "X"); (expr.var "X")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]).

(* valueFlow(X, X) :- assign(Y, X). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "X"); (expr.var "X")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "Y"); (expr.var "X")] |}
    ]).

(* valueFlow(X, Y) :- assign(X, Z), memoryAlias(Z, Y). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "X"); (expr.var "Z")] |};
      {| clause.rel := "memoryAlias"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

(* valueFlow(X, Y) :- valueFlow(X, Z), valueFlow(Z, Y). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "X"); (expr.var "Z")] |};
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), valueFlow(Z, Y). *)
Definition rule_5 : rule :=
rule.impl ([
      {| clause.rel := "valueAlias"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "Z"); (expr.var "X")] |};
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "Z"); (expr.var "Y")] |}
    ]).

(* valueAlias(X, Y) :- valueFlow(Z, X), memoryAlias(Z, W), valueFlow(W, Y). *)
Definition rule_6 : rule :=
rule.impl ([
      {| clause.rel := "valueAlias"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]) ([
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "Z"); (expr.var "X")] |};
      {| clause.rel := "memoryAlias"; clause.args := [(expr.var "Z"); (expr.var "W")] |};
      {| clause.rel := "valueFlow"; clause.args := [(expr.var "W"); (expr.var "Y")] |}
    ]).

(* memoryAlias(X, X) :- assign(Y, X). *)
Definition rule_7 : rule :=
rule.impl ([
      {| clause.rel := "memoryAlias"; clause.args := [(expr.var "X"); (expr.var "X")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "Y"); (expr.var "X")] |}
    ]).

(* memoryAlias(X, X) :- assign(X, Y). *)
Definition rule_8 : rule :=
rule.impl ([
      {| clause.rel := "memoryAlias"; clause.args := [(expr.var "X"); (expr.var "X")] |}
    ]) ([
      {| clause.rel := "assign"; clause.args := [(expr.var "X"); (expr.var "Y")] |}
    ]).

(* memoryAlias(X, W) :- dereference(Y, X), valueAlias(Y, Z), dereference(Z, W). *)
Definition rule_9 : rule :=
rule.impl ([
      {| clause.rel := "memoryAlias"; clause.args := [(expr.var "X"); (expr.var "W")] |}
    ]) ([
      {| clause.rel := "dereference"; clause.args := [(expr.var "Y"); (expr.var "X")] |};
      {| clause.rel := "valueAlias"; clause.args := [(expr.var "Y"); (expr.var "Z")] |};
      {| clause.rel := "dereference"; clause.args := [(expr.var "Z"); (expr.var "W")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4;
   rule_5;
   rule_6;
   rule_7;
   rule_8;
   rule_9].

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