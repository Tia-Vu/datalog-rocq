From Stdlib Require Import List.
From DatalogRocq Require Import Dataflow GridGraph DependencyGenerator ATLDatalogParams Matmul.
From Datalog Require Import CompilerExamples.
From coqutil Require Import Map.Interface Map.Properties Map.Solver.
Import ListNotations.

Definition three_three_dims : list nat := [3; 3].

Definition three_three_grid_graph := GridGraph three_three_dims.

Definition indexed_layout : list (Node * list nat) := [].

Definition layout (n : Node) : list rule := 
 match find (fun p => if GridGraph.node_eqb (fst p) n then true else false) indexed_layout with
  | None => []
  | Some (_, ris) =>
      map (fun ri => nth ri datalog_matmul empty_rule) ris
  end.

Theorem good_layout :
  Dataflow.good_layout layout three_three_grid_graph.(nodes) datalog_matmul.
Proof.
    unfold Dataflow.good_layout.
    split.
    - apply Forall_forall. intros. admit.
    - intros. split.
Admitted.