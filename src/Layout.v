From Stdlib Require Import Strings.String.
From Stdlib.Lists Require Import List.
From DatalogRocq Require Import Dataflow.
From DatalogRocq Require Import ComputeCore.

Definition rel := string.
Definition var := string.
Definition fn := string.
Definition agg := unit.
Definition T := nat.  (* semantic domain for interpretation *)
Definition program := list (Datalog.rule rel var fn agg).

(* A layout is a mapping from compute cores to the rules that they have *)
Definition layout (program : program) (network : dataflow_network) := core_id -> list (Datalog.rule rel var fn agg).

(* A valid layout is one where every rule is assigned to some core  *)
Definition layout_assigns_all_rules (program : program) (network : dataflow_network) (l : layout program network) :=
  (forall r, In r program -> exists c, In r (l c)) /\
  (forall c1 c2 r, In r (l c1) -> In r (l c2) -> c1 = c2).


Definition valid_layout (program : program) (network : dataflow_network) (l : layout program network) :=
  layout_assigns_all_rules program network l.



