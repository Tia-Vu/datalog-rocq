From Stdlib Require Import List Bool Lia.
From Datalog Require Import Datalog.
From DatalogRocq Require Import Dataflow GridGraph DependencyGenerator.
Import ListNotations.

Module GridLayout (Params : DatalogParams).
  Import Params.
  Parameter (dims : list nat).
  Definition rule := Datalog.rule rel var fn aggregator.
  Parameter (program : list rule).
  Parameter (indexed_layout : list (Node * list nat)).
  Module dependency_generator := DependencyGenerator(Params).

  Definition grid_graph : Dataflow.Graph := GridGraph dims.

  Definition layout (n : Node) : list rule :=
    if check_node_in_bounds dims n then
      match find (fun p => GridGraph.node_eqb (fst p) n) indexed_layout with
      | None => []
      | Some (_, ris) =>
          fold_right
            (fun ri acc =>
               match nth_error program ri with
               | Some r => r :: acc
               | None => acc
               end)
            [] ris
      end
    else [].

  Definition rule_in_layout (r : rule) : bool :=
    existsb (fun n => existsb (dependency_generator.rule_eqb r) (layout n))
            (all_nodes_h dims).

  Definition node_rules_ok (n : Node) : bool :=
    forallb (fun r => existsb (dependency_generator.rule_eqb r) program)
            (layout n).

  Definition check_layout : bool :=
    forallb node_rules_ok (all_nodes_h dims) &&
    forallb rule_in_layout program.

  Lemma layout_nonempty_only_valid_nodes :
    forall n r,
      In r (layout n) ->
      GridGraph.is_graph_node dims n.
  Proof.
    intros n r Hlayout.
    unfold layout in Hlayout.
    destruct (check_node_in_bounds dims n) eqn:Hbounds; try discriminate.
    - apply GridGraph.check_node_in_bounds_h_correct; eauto.
    - contradiction.
  Qed.

Theorem good_layout :
  check_layout = true ->
  Dataflow.good_layout layout grid_graph.(nodes) program.
Proof.
    unfold check_layout.
    unfold Dataflow.good_layout.
    intros.
    split.
    - apply Forall_forall. intros. apply andb_true_iff in H. destruct H as [H_nodes_ok H_rule_in_layout].
      rewrite forallb_forall in H_rule_in_layout.
      apply H_rule_in_layout in H0 as H_layout.
      unfold rule_in_layout in H_layout. rewrite existsb_exists in H_layout.
      destruct H_layout as [n [H_n_in_nodes H_r_in_layout]].
      rewrite existsb_exists in H_r_in_layout.
      destruct H_r_in_layout as [r H_r_eq].
      exists n. destruct H_r_eq as [Hin H_r_eq]. 
      destruct (dependency_generator.rule_eqb_spec x r).
      + subst. split; auto. apply all_nodes_correct. apply H_n_in_nodes.
      + discriminate H_r_eq.
    - intros.
      apply andb_true_iff in H. destruct H as [H_nodes_ok H_rule_in_layout].
      rewrite forallb_forall in H_nodes_ok.
      rewrite forallb_forall in H_rule_in_layout.
      split.
      + apply layout_nonempty_only_valid_nodes in H0 as H_layout_nonempty.
        auto.
      + apply layout_nonempty_only_valid_nodes in H0 as H_layout_nonempty.
        apply all_nodes_correct in H_layout_nonempty.
        specialize (H_nodes_ok n H_layout_nonempty).
        unfold node_rules_ok in H_nodes_ok.
        rewrite forallb_forall in H_nodes_ok.
        specialize (H_nodes_ok r H0).
        rewrite existsb_exists in H_nodes_ok.
        destruct H_nodes_ok as [r' H_r'_in_program].
        destruct H_r'_in_program as [Hin H_r_eq].
        destruct (dependency_generator.rule_eqb_spec r r').
        * subst. auto.
        * discriminate H_r_eq.
Qed.

End GridLayout.