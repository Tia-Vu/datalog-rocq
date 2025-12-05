From Datalog Require Import CompilerExamples.
From Stdlib Require Import Strings.String.
From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Datalog Require Import FancyNotations.
From DatalogRocq Require Import ATLDatalogParams.
From DatalogRocq Require Import DependencyGenerator.
Import ListNotations.
Import ATLToDatalog.
Open Scope string_scope.

Import ATLDatalogParams.
Module ATLDatalogDependencyGenerator := DependencyGenerator(ATLDatalogParams).
Compute ATLDatalogDependencyGenerator.get_program_dependencies datalog_matmul.
Definition empty_rule : rule :=
  datalog_rule:( [ ] :- [ ] ).

Compute (length datalog_matmul).
Compute ATLDatalogDependencyGenerator.get_rule_dependencies
        datalog_matmul
        (nth 3 datalog_matmul empty_rule).
Compute ATLDatalogDependencyGenerator.get_program_dependencies_flat datalog_matmul.
Print datalog_matmul.