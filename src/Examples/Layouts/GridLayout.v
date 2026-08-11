From Stdlib Require Import List Bool Lia Relation_Operators.
From Datalog Require Import Datalog.
From DatalogRocq Require Import DistributedDatalog Topologies.Graph GridGraph.
From coqutil Require Import Map.Interface Eqb.
Import ListNotations.

Section GridLayout.
  Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
  Context `{sig : signature fn aggregator T} `{query_sig : query_signature rel}.
  Context {context : map.map var T} {context_ok : map.ok context}.
  Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
  Context {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.
  Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.
  Context {aggregator_eqb : Eqb aggregator} {aggregator_eqb_ok : Eqb_ok aggregator_eqb}.

  Definition rule := @Datalog.rule rel var fn aggregator.

  Context {rule_eqb : rule -> rule -> bool}.
  Context {rule_eqb_spec : forall r1 r2 : rule,
                            BoolSpec (r1 = r2) (r1 <> r2) (rule_eqb r1 r2)}.

  Definition mk_grid_graph (dims : list nat) : Graph := GridGraph dims.

  Definition mk_layout_from_indexed_layout (dims : list nat) (indexed_layout : list (Node * list nat)) (program : list rule) (n : Node) : list rule :=
      if check_node_in_bounds dims n then
      match find (fun p => eqb (fst p) n) indexed_layout with
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

  (* Just putting in some dummy values for now *)
  Definition mk_always_forward_table (dims : list nat) (n : Node) : rel -> Node -> list Node :=
    fun f s => filter (GridGraph.is_neighbor dims n) (all_nodes_h dims).

  Definition mk_no_input_fn (n : Node) (f : @Datalog.fact rel T) : Prop := False.

  Definition mk_all_output_fn (n : Node) (f : rel) : Prop := True.


  Definition mk_dataflow_network
             (dims : list nat)
             (indexed_layout : list (Node * list nat))
             (program : list rule) : DistributedDatalog.DataflowNetwork :=
    {|
      DistributedDatalog.graph := mk_grid_graph dims;
      DistributedDatalog.layout := mk_layout_from_indexed_layout dims indexed_layout program;
      DistributedDatalog.forward := mk_always_forward_table dims;
      DistributedDatalog.input := mk_no_input_fn;
      DistributedDatalog.output := mk_all_output_fn
    |}.

  Definition rule_in_layout (r : rule) (layout : Node -> list rule) (dims : list nat): bool :=
    existsb (fun n => existsb (rule_eqb r) (layout n))
            (all_nodes_h dims).

  Definition node_rules_ok (n : Node) (layout : Node -> list rule) (program : list rule): bool :=
    forallb (fun r => existsb (rule_eqb r) program)
            (layout n).

  Definition check_layout (dims : list nat) (layout : Node -> list rule) (program : list rule) : bool :=
    forallb (fun n => node_rules_ok n layout program) (all_nodes_h dims) &&
    forallb (fun r => rule_in_layout r layout dims) program.

  Lemma layout_nonempty_only_valid_nodes :
    forall n r dims indexed_layout program,
      In r (mk_layout_from_indexed_layout dims indexed_layout program n) ->
      GridGraph.is_graph_node dims n.
  Proof.
    intros n r dims indexed_layout program Hlayout.
    unfold mk_layout_from_indexed_layout in Hlayout.
    destruct (check_node_in_bounds dims n) eqn:Hbounds; try discriminate.
    - apply GridGraph.check_node_in_bounds_h_correct; eauto.
    - contradiction.
  Qed.

Theorem good_layout :
    forall dims indexed_layout program,
    check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
    DistributedDatalog.good_layout (mk_layout_from_indexed_layout dims indexed_layout program) (GridGraph dims).(nodes) program.
Proof.
    unfold check_layout.
    unfold DistributedDatalog.good_layout.
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

(* In GridLayout section, convert grid_reachable to forwarding_reachable *)
Lemma grid_reachable_to_forwarding :
  forall dims0 r s n1 n2,
    GridGraph.grid_reachable dims0 n1 n2 ->
    forwarding_reachable (mk_always_forward_table dims0) r s n1 n2.
Proof.
  intros dims0 r s n1 n2 Hreach.
  induction Hreach.
  - apply rt1n_refl.
  - eapply rt1n_trans; [| exact IHHreach].
    unfold DistributedDatalog.forwards_rel, mk_always_forward_table.
    apply filter_In. split.
    + apply GridGraph.all_nodes_h_correct. inversion H; eauto.
    + apply GridGraph.is_neighbor_correct. exact H.
Qed.

Lemma good_forwarding_complete_grid :
  forall dims0 indexed_layout program,
    check_layout dims0 (mk_layout_from_indexed_layout dims0 indexed_layout program) program = true ->
    good_forwarding_complete (mk_dataflow_network dims0 indexed_layout program).
Proof.
  intros dims0 indexed_layout program Hcheck.
  unfold good_forwarding_complete.
  simpl. intros rel0.
  split.
  - intros n_prod n_cons Hprod Hcons.
  assert (Hn_prod : GridGraph.is_graph_node dims0 n_prod).
  { destruct Hprod as [r [Hin_layout _]].
    eapply layout_nonempty_only_valid_nodes; apply Hin_layout. }
  assert (Hn_cons : GridGraph.is_graph_node dims0 n_cons).
  { destruct Hcons as [r [Hin_layout _]].
    eapply layout_nonempty_only_valid_nodes; apply Hin_layout. }
  eapply grid_reachable_to_forwarding.
  apply GridGraph.grid_connected; auto.
  - intros n_prod Hprod. exists n_prod. split.
    + simpl. unfold mk_all_output_fn. auto.
    + apply rt1n_refl.
Qed.

Lemma good_network :
  forall dims indexed_layout program,
  check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
  DistributedDatalog.good_network (mk_dataflow_network dims indexed_layout program) program.
Proof.
  intros dims indexed_layout program Hcheck.
  unfold mk_dataflow_network. unfold good_network.
  split.
  - apply GridGraph.good_graph.
  - split. 
    + apply good_layout. assumption.
    + split.
      * simpl. unfold good_forwarding. unfold good_forwarding_sound.
        split.
        ** intros. unfold mk_always_forward_table in H.
        apply filter_In in H.
        destruct H as [Hneighbor Hin].
        apply GridGraph.is_neighbor_correct in Hin.
        exact Hin.
        ** apply good_forwarding_complete_grid; auto.
      * split.
        ** simpl. unfold good_input. intros. inversion H.
        ** simpl. unfold good_output. intros. exists n. split.
            --- destruct H as [r [Hin_layout _]].
             apply layout_nonempty_only_valid_nodes in Hin_layout.
             exact Hin_layout.
           --- simpl. unfold mk_all_output_fn. trivial.
Qed.


End GridLayout.
