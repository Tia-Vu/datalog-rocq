From Stdlib Require Import List Bool Lia.
From Datalog Require Import Datalog.
From DatalogRocq Require Import Dataflow GridGraph.
From coqutil Require Import Map.Interface.
Import ListNotations.

Section GridLayout.
  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : var -> var -> bool} {var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0)}.
  Context {rel_eqb : rel -> rel -> bool} {rel_eqb_spec : forall x0 y0 : rel, BoolSpec (x0 = y0) (x0 <> y0) (rel_eqb x0 y0)}.
  Context {fn_eqb : fn -> fn -> bool} {fn_eqb_spec : forall x0 y0 : fn, BoolSpec (x0 = y0) (x0 <> y0) (fn_eqb x0 y0)}.
  Context {aggregator_eqb : aggregator -> aggregator -> bool}
          {aggregator_eqb_spec : forall x0 y0 : aggregator, BoolSpec (x0 = y0) (x0 <> y0) (aggregator_eqb x0 y0)}.

  Definition rule := Datalog.rule rel var fn aggregator.

  Context {rule_eqb : rule -> rule -> bool}.
  Context {rule_eqb_spec : forall r1 r2 : rule,
                            BoolSpec (r1 = r2) (r1 <> r2) (rule_eqb r1 r2)}.

  Parameter (dims : list nat).
  Parameter (program : list rule).
  Parameter (indexed_layout : list (Node * list nat)).

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
    existsb (fun n => existsb (rule_eqb r) (layout n))
            (all_nodes_h dims).

  Definition node_rules_ok (n : Node) : bool :=
    forallb (fun r => existsb (rule_eqb r) program)
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
      destruct (rule_eqb_spec x r).
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
        destruct (rule_eqb_spec r r').
        * subst. auto.
        * discriminate H_r_eq.
Qed.

Definition always_forward_table (n : Node) : rel * (list T) -> list Node :=
  fun f => filter (GridGraph.is_neighbor dims n) (all_nodes_h dims).

Definition no_inputs (n : Node) (f : rel * (list T)) : Prop := False.

Definition all_outputs (n : Node) (f : rel * (list T)) : Prop := True.
  
Definition DataflowNetwork : Dataflow.DataflowNetwork :=
  {|
    Dataflow.graph := grid_graph;
    Dataflow.layout := layout;
    Dataflow.forward := always_forward_table;
    Dataflow.input := no_inputs;
    Dataflow.output := all_outputs
  |}.

Lemma good_network :
  check_layout = true ->
  Dataflow.good_network DataflowNetwork program.
Proof.
  intros Hcheck.
  unfold DataflowNetwork. unfold good_network.
  split.
  - apply GridGraph.good_graph.
  - split. 
    + apply good_layout. assumption.
    + split.
      * simpl. unfold good_forwarding. intros. unfold always_forward_table in H.
        apply filter_In in H.
        destruct H as [Hneighbor Hin].
        apply GridGraph.is_neighbor_correct in Hin.
        split; try inversion Hin; auto.
      * simpl. unfold good_input. intros. inversion H.
Qed.

Theorem soundness :
  forall f : rel * list T,
    check_layout = true ->
    network_prog_impl_fact DataflowNetwork f ->
    prog_impl_fact program f.
Proof.
  intros.
  apply (Dataflow.soundness DataflowNetwork program); auto.
  apply good_network; auto.
Qed.

End GridLayout.