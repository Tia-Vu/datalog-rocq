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

Module family_examples.

(* Individual rules using fancy Datalog notation *)

Definition r_ancestor1 : rule :=
  datalog_rule:( [ ancestor($x, $y) ] :- [ parent($x, $y) ] ).

Definition r_ancestor2 : rule :=
  datalog_rule:( [ ancestor($x, $y) ] :- [ parent($x, $z); ancestor($z, $y) ] ).

Definition r_sibling : rule :=
  datalog_rule:( [ sibling($x, $y) ] :- [ parent($p, $x); parent($p, $y) ] ).

Definition r_aunt_uncle : rule :=
  datalog_rule:( [ aunt_uncle($x, $y) ] :- [ sibling($x, $p); parent($p, $y) ] ).

Definition r_cousin : rule :=
  datalog_rule:( [ cousin($x, $y) ] :- [ parent($px, $x); parent($py, $y); sibling($px, $py) ] ).

(* The full program, referencing the rules directly *)
Definition family_program : list rule :=
  [ r_ancestor1;
    r_ancestor2;
    r_sibling;
    r_aunt_uncle;
    r_cousin ].

End family_examples.

Compute StringDependencyGenerator.get_program_dependencies family_examples.family_program.
Compute StringDependencyGenerator.get_rule_dependencies
        family_examples.family_program
        family_examples.r_ancestor2.

Compute StringDependencyGenerator.get_program_dependencies_flat
        family_examples.family_program.