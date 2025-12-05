From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Datalog Require Import FancyNotations.
From DatalogRocq Require Import StringDatalogParams.
From DatalogRocq Require Import DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.
Module StringDependencyGenerator := DependencyGenerator(StringDatalogParams).

Definition path_base_r : rule := datalog_rule:([ Path($a, $b) ] :- [ Edge($a, $b) ]).
Definition path_step_r : rule := datalog_rule:([ Path($a, $c) ] :- [ Edge($a, $b); Path($b, $c) ]).
Definition two_step_r : rule := datalog_rule:([ TwoStep($a, $c) ] :- [ Edge($a, $b); Edge($b, $c) ]).
Definition cycle_r : rule := datalog_rule:([ Cycle($a) ] :- [ Path($a, $a) ]).
Definition triangle_r : rule := datalog_rule:([ Triangle($a, $b) ] :- [ Edge($a, $b); Edge($b, $c); Edge($c, $a) ]).
Definition bipath_r : rule := datalog_rule:([ BiPath($a, $b) ] :- [ Path($a, $b); Path($b, $a) ]).

Definition graph_program : list rule :=
   [ path_base_r;
    path_step_r;
    two_step_r;
    cycle_r;
    triangle_r;
    bipath_r ].

Definition name_overrides : list (rule * string) :=
  [ (path_base_r, "path_base");
    (path_step_r, "path_step");
    (two_step_r, "two_step");
    (cycle_r, "cycle");
    (triangle_r, "triangle");
    (bipath_r, "bipath")
  ].

Compute StringDependencyGenerator.get_program_dependencies graph_program.
Compute StringDependencyGenerator.get_program_dependencies_flat graph_program.