From Stdlib Require Import List Bool Lia Relation_Operators.
From Datalog Require Import Datalog.
From Datalog.Util Require Import List.
From DatalogRocq Require Import DistributedDatalog Topologies.Graph GridGraph.
From coqutil Require Import Map.Interface Eqb Tactics.fwd.
Import ListNotations.

Section GridLayout.
  Context `{params : datalog_params}.

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
  Definition mk_always_forward_table (dims : list nat) (n : Node) : rel -> list Node :=
    fun f => filter (GridGraph.is_neighbor dims n) (all_nodes_h dims).

  Definition mk_no_input_fn (n : Node) (f : Datalog.fact) : Prop := False.

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

  (*----------------------------------------------------------------------------*)
  (* Decidable [good_layout] check, over a plain node enumeration [all_nodes]    *)
  (* (no topology record): (1) every rule placed on an enumerated node is a      *)
  (* program rule, and (2) every program rule is placed on some enumerated node. *)
  (*----------------------------------------------------------------------------*)
  Definition node_rules_okb (layout : Node -> list rule) (program : list rule) (n : Node) : bool :=
    forallb (fun r => inb r program) (layout n).
  Definition rule_in_layoutb (all_nodes : list Node) (layout : Node -> list rule) (r : rule) : bool :=
    existsb (fun n => inb r (layout n)) all_nodes.
  Definition good_layoutb (all_nodes : list Node) (layout : Node -> list rule) (program : list rule) : bool :=
    forallb (node_rules_okb layout program) all_nodes &&
    forallb (rule_in_layoutb all_nodes layout) program.

  Lemma good_layoutb_sound (all_nodes : list Node) (nodes : Node -> Prop) (layout : Node -> list rule)
      (program : list rule) :
    (forall n, In n all_nodes <-> nodes n) ->
    (forall n r, In r (layout n) -> nodes n) ->
    good_layoutb all_nodes layout program = true ->
    good_layout layout nodes program.
  Proof.
    intros Hspec Hvalid Hcheck. unfold good_layoutb in Hcheck. fwd.
    rewrite Forall_forall in Hcheckp0, Hcheckp1. split.
    - apply Forall_forall. intros r Hr. apply Hcheckp1 in Hr. cbv [rule_in_layoutb] in Hr. fwd.
      eexists. split; [apply Hspec |]; eassumption.
    - intros n r Hr. pose proof (Hvalid n r Hr) as Hn. split; [exact Hn |].
      apply Hspec, Hcheckp0 in Hn. cbv [node_rules_okb] in Hn. fwd.
      rewrite Forall_forall in Hn. apply Hn in Hr. fwd. assumption.
  Qed.

Theorem good_layout :
    forall dims indexed_layout program,
    good_layoutb (all_nodes_h dims) (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
    DistributedDatalog.good_layout (mk_layout_from_indexed_layout dims indexed_layout program) (GridGraph dims).(nodes) program.
Proof.
  intros dims indexed_layout program H. apply good_layoutb_sound with (all_nodes := all_nodes_h dims).
  - intros n. symmetry. apply all_nodes_correct.
  - intros n r Hr. exact (layout_nonempty_only_valid_nodes n r dims indexed_layout program Hr).
  - exact H.
Qed.

(* In GridLayout section, convert grid_reachable to forwarding_reachable *)
Lemma grid_reachable_to_forwarding :
  forall dims0 r n1 n2,
    GridGraph.grid_reachable dims0 n1 n2 ->
    forwarding_reachable (mk_always_forward_table dims0) r n1 n2.
Proof.
  intros dims0 r n1 n2 Hreach.
  induction Hreach.
  - apply rt1n_refl.
  - eapply rt1n_trans; [| exact IHHreach].
    unfold forwards_rel, mk_always_forward_table.
    apply filter_In. split.
    + apply GridGraph.all_nodes_h_correct. inversion H; eauto.
    + apply GridGraph.is_neighbor_correct. exact H.
Qed.

Lemma good_forwarding_complete_grid :
  forall dims0 indexed_layout program,
    good_forwarding_complete (mk_dataflow_network dims0 indexed_layout program).
Proof.
  intros dims0 indexed_layout program.
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
  good_layoutb (all_nodes_h dims) (mk_layout_from_indexed_layout dims indexed_layout program) program = true ->
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
        split; try inversion Hin; auto.
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
