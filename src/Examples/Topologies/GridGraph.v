From Stdlib Require Import List Bool ZArith.Znat Lia.
From DatalogRocq Require Import Dataflow.
From coqutil Require Import Datatypes.List.
Import ListNotations.

Section GridGraph.

  Definition Node : Type := list nat.
  Definition Dimensions : Type := list nat.

  Variable dims : Dimensions.

  Definition node_eqb (n1 n2 : Node) : bool := list_eqb Nat.eqb n1 n2.

  Lemma node_eqb_spec :
    forall n1 n2 : Node,
      BoolSpec (n1 = n2) (n1 <> n2) (node_eqb n1 n2).
  Proof.
    unfold node_eqb.
    apply list_eqb_spec.
  Qed.

  Inductive is_graph_node : Dimensions -> Node -> Prop :=
  | valid_nil : is_graph_node [] []
  | valid_cons : forall (d : nat) (ds : list nat) (coord : nat) (rest : Node),
      coord < d ->
      is_graph_node ds rest ->
      is_graph_node (d :: ds) (coord :: rest).

  Fixpoint check_node_in_bounds_h (coords dims : list nat) : bool :=
    match coords, dims with
    | [], [] => true
    | c :: cs, d :: ds => (c <? d) && check_node_in_bounds_h cs ds
    | _, _ => false
    end. 

  Definition check_node_in_bounds (n : Node) : bool :=
    check_node_in_bounds_h n dims.

  Lemma check_node_in_bounds_h_correct :
    forall n dims0,
      is_graph_node dims0 n <-> check_node_in_bounds_h n dims0 = true.
  Proof.
    intros n. split.
    - intros Hnode.
      induction Hnode.
      + simpl. reflexivity.
      + simpl. apply andb_true_iff. split.
        * apply Nat.ltb_lt. assumption.
        * apply IHHnode.
    - revert n.
      induction dims0 as [| d ds IH]; intros n Hcheck.
      + destruct n; [constructor | simpl in Hcheck; inversion Hcheck].
      + destruct n as [| c cs].
        * simpl in Hcheck. inversion Hcheck.
        * simpl in Hcheck. apply andb_true_iff in Hcheck. destruct Hcheck as [Hc Hrest].
          apply Nat.ltb_lt in Hc.
          constructor; try assumption.
          apply IH. assumption.
  Qed.

  Lemma check_node_in_bounds_correct :
    forall n,
      is_graph_node dims n <-> check_node_in_bounds n = true.
  Proof.
    intros n.
    apply check_node_in_bounds_h_correct.
  Qed.

  Definition abs (c1 c2 : nat) : nat := Nat.max (c1 - c2) (c2 - c1).

  (* This definition says if a node is n steps away from another node by manhattan distance,
     and here we don't care about the dimensions *)
  Inductive manhattan_distance : nat -> Node -> Node -> Prop := 
  | neighbor_zero_steps : forall n,
      manhattan_distance 0 n n
  | neighbor_steps : forall prev_diff next_coord_diff n1 n2 c1 c2,
      manhattan_distance prev_diff n1 n2 -> 
      abs c1 c2 = next_coord_diff -> 
      manhattan_distance (prev_diff + next_coord_diff) (c1 :: n1) (c2 :: n2).
    
  (* Simple adjacency: differs by +1 on exactly one coordinate *)
  Inductive is_graph_edge : Dimensions -> Node -> Node -> Prop := 
  | valid_edge : forall (dims : Dimensions) (u v : Node),
                 is_graph_node dims u ->
                 is_graph_node dims v -> 
                 manhattan_distance 1 u v ->
                 is_graph_edge dims u v.

  Fixpoint is_mth_neighbor (n1 n2 : Node) (m : nat) : bool :=
    match n1, n2 with 
    | [], [] => if m =? 0 then true else false
    | c :: cs, c' :: cs' => 
      if m <? (abs c c') then false 
      else is_mth_neighbor cs cs' (m - (abs c c'))
    | _, _ => false
    end.

  Definition is_neighbor (n1 n2 : Node) : bool :=
   check_node_in_bounds n1 &&
   check_node_in_bounds n2 &&
   is_mth_neighbor n1 n2 1.


  Lemma abs_same : forall n, abs n n = 0.
  Proof. 
    induction n; auto. 
  Qed.

  Lemma is_mth_neighbor_self : forall n,
    is_mth_neighbor n n 0 = true.
  Proof.
    induction n; auto.
    simpl. rewrite abs_same. simpl.
    apply IHn.
  Qed.

  Lemma is_mth_neighbor_is_manhattan_distance : forall n1 n2 m, 
    is_mth_neighbor n1 n2 m = true <-> manhattan_distance m n1 n2.
  Proof.
    split.
    - revert n2. revert m. induction n1; intros m n2 H.
      + destruct n2; simpl in H.
        * destruct m; try discriminate. econstructor.
        * destruct m; try discriminate.
      + destruct n2.
        * simpl in H. discriminate.
        * simpl in H. destruct (m <? abs a n) eqn:Hcomp; try discriminate.
          assert (abs a n <= m) by (apply Nat.ltb_ge; exact Hcomp).
          replace m with ((m - (abs a n)) + (abs a n)) by lia.
          econstructor; eauto.
    - induction 1.
      + apply is_mth_neighbor_self.
      + simpl. subst. assert (prev_diff + abs c1 c2 <? abs c1 c2 = false).
        { apply Nat.ltb_ge. lia. }
        rewrite H0. rewrite Nat.add_sub; try lia.
        apply IHmanhattan_distance.
  Qed.

  Lemma is_neighbor_correct : forall n1 n2,
    is_neighbor n1 n2 = true <-> is_graph_edge dims n1 n2.
  Proof.
    intros n1 n2. split.
    - intros Hneighbor.
      unfold is_neighbor in Hneighbor.
      apply andb_true_iff in Hneighbor.
      destruct Hneighbor as [Hrest Hmth].
      apply andb_true_iff in Hrest.
      destruct Hrest as [Hn1 Hn2].
      apply check_node_in_bounds_correct in Hn1.
      apply check_node_in_bounds_correct in Hn2.
      apply is_mth_neighbor_is_manhattan_distance in Hmth.
      econstructor; eauto.
    - intros Hedge.
      unfold is_neighbor.
      apply andb_true_iff. split.
      + apply andb_true_iff. split.
        * apply check_node_in_bounds_correct. inversion Hedge; assumption.
        * apply check_node_in_bounds_correct. inversion Hedge; assumption.
      + apply is_mth_neighbor_is_manhattan_distance. inversion Hedge; assumption.
  Qed.

  (* The actual graph *)
  Definition GridGraph : Dataflow.Graph :=
    {|
      nodes := is_graph_node dims;
      edge  := is_graph_edge dims
    |}.

  Theorem good_graph : Dataflow.good_graph GridGraph.
  Proof.
    unfold Dataflow.good_graph.
    intros n1 n2 Hedge.
    split; inversion Hedge; assumption.
  Qed.

  Definition add_dimension (ln : list Node) (i : nat) : list Node :=
    map (fun n => i :: n) ln.

  Lemma add_dimension_length :
    forall (ln : list Node) (i : nat),
      length (add_dimension ln i) = length ln.
  Proof.
    intros. induction ln; eauto.
    simpl. rewrite IHln. reflexivity.
  Qed.

  Fixpoint all_nodes_h (dims : list nat) : list Node :=
    match dims with
    | [] => [[]]
    | d :: ds =>
        let rest := all_nodes_h ds in
        flat_map (add_dimension rest) (seq 0 d)
    end.
  
  Definition all_nodes : list Node := all_nodes_h dims.

  Lemma all_nodes_h_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes_h dims).
  Proof.
    intros n. split.
    - intros Hnode.
      induction Hnode.
      + simpl. left. reflexivity.
      + simpl. apply in_flat_map. 
        exists coord. split.
        * apply in_seq. simpl. lia.
        * apply in_map. apply IHHnode.
    - revert n.
      induction dims as [| d ds IH]; intros n Hin; simpl in Hin.
    + destruct Hin as [H | H]; [subst; constructor | inversion H].
    + apply in_flat_map in Hin.
      destruct Hin as [r [Hin_seq Hin_map]].
      apply in_map_iff in Hin_map.
      destruct Hin_map as [rest [Heq Hin_rest]].
      subst n.
      constructor.
      * apply in_seq in Hin_seq. lia.
      * apply IH. assumption.
  Qed.

  Theorem all_nodes_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes).
  Proof.
    intros n. unfold all_nodes.
    apply all_nodes_h_correct.
  Qed.

  Lemma length_flatmap_nonzero :
    forall (A B : Type) (f : A -> list B) (l : list A),
      (exists a, In a l /\ length (f a) > 0) ->
      length (flat_map f l) > 0.
  Proof.
    induction l; simpl; intros.
    - destruct H. destruct H. destruct H.
    - rewrite length_app. destruct H.
      destruct H. destruct H.
      + subst. lia.
      + assert (length (flat_map f l) > 0).
        { apply IHl; exists x; split; assumption. }
        lia.
  Qed.
  
  Theorem all_nodes_nonzero_dim_nonempty :
    forall dims0,
      (forall d, In d dims0 -> d > 0) ->
      length (all_nodes_h dims0) > 0.
  Proof.
    intros. induction dims0.
    - simpl. lia.
    - simpl. apply length_flatmap_nonzero. destruct a.
      + specialize (H 0). simpl in H. lia.
      + exists 0. split.
        * apply in_seq. lia.
        * intros. rewrite add_dimension_length. apply IHdims0.
          intros. apply H. right. assumption.
  Qed.

  (* Fixpoint all_edges_h (dims : list nat) : list (Node * Node) :=
    match dims with
    | [] => []
    | d :: ds =>
        let rest_nodes := all_nodes_h ds in
        let lower_dim_edges := all_edges_h ds in
        let edges_in_current_dim :=
          flat_map (fun c =>
            flat_map (fun n =>
              match n with
              | [] => []
              | _ :: _ =>
                  let u := c :: n in
                  let v := (c + 1) :: n in
                  if (c + 1 <? d)
                  then [(u, v); (v, u)]
                  else []
              end) rest_nodes) (seq 0 d) in
        edges_in_current_dim ++ lower_dim_edges
    end. *)

  (* Definition visit_graph_nodes (f : Node -> unit) : unit :=
  List.iter (fun n => if check_node_in_bounds n then f n else tt) (all_nodes dims).
 *)

End GridGraph.