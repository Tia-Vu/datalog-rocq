(* Auto-generated from SouffleExamples/pointsto.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
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
(* .type Variable <: symbol  {-> string} *)
(* .type Allocation <: symbol  {-> string} *)
(* .type Field <: symbol  {-> string} *)
(* .decl  AssignAlloc(var:Variable{->string}, heap:Allocation{->string}) *)
(* .decl  Assign(source:Variable{->string}, destination:Variable{->string}) *)
(* .decl  PrimitiveAssign(source:Variable{->string}, dest:Variable{->string}) *)
(* .decl  Load(base:Variable{->string}, dest:Variable{->string}, field:Field{->string}) *)
(* .decl  Store(source:Variable{->string}, base:Variable{->string}, field:Field{->string}) *)
(* .decl  VarPointsTo(var:Variable{->string}, heap:Allocation{->string}) *)
(* .decl  Alias(x:Variable{->string}, y:Variable{->string}) *)

(* Assign(var1, var2) :- PrimitiveAssign(var1, var2). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "Assign"; clause.args := [(expr.var "var1"); (expr.var "var2")] |}
    ]) ([
      {| clause.rel := "PrimitiveAssign"; clause.args := [(expr.var "var1"); (expr.var "var2")] |}
    ]).

(* Alias(instanceVar, iVar) :- VarPointsTo(instanceVar, instanceHeap), VarPointsTo(iVar, instanceHeap). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "Alias"; clause.args := [(expr.var "instanceVar"); (expr.var "iVar")] |}
    ]) ([
      {| clause.rel := "VarPointsTo"; clause.args := [(expr.var "instanceVar"); (expr.var "instanceHeap")] |};
      {| clause.rel := "VarPointsTo"; clause.args := [(expr.var "iVar"); (expr.var "instanceHeap")] |}
    ]).

(* VarPointsTo(var, heap) :- AssignAlloc(var, heap). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "VarPointsTo"; clause.args := [(expr.var "var"); (expr.var "heap")] |}
    ]) ([
      {| clause.rel := "AssignAlloc"; clause.args := [(expr.var "var"); (expr.var "heap")] |}
    ]).

(* VarPointsTo(var1, heap) :- Assign(var2, var1), VarPointsTo(var2, heap). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "VarPointsTo"; clause.args := [(expr.var "var1"); (expr.var "heap")] |}
    ]) ([
      {| clause.rel := "Assign"; clause.args := [(expr.var "var2"); (expr.var "var1")] |};
      {| clause.rel := "VarPointsTo"; clause.args := [(expr.var "var2"); (expr.var "heap")] |}
    ]).

(* Assign(var1, var2) :- Store(var1, instanceVar2, field), Alias(instanceVar2, instanceVar1), Load(instanceVar1, var2, field). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "Assign"; clause.args := [(expr.var "var1"); (expr.var "var2")] |}
    ]) ([
      {| clause.rel := "Store"; clause.args := [(expr.var "var1"); (expr.var "instanceVar2"); (expr.var "field")] |};
      {| clause.rel := "Alias"; clause.args := [(expr.var "instanceVar2"); (expr.var "instanceVar1")] |};
      {| clause.rel := "Load"; clause.args := [(expr.var "instanceVar1"); (expr.var "var2"); (expr.var "field")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4].

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