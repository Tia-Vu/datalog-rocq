From Stdlib Require Import List Bool ZArith.Znat.
From DatalogRocq Require Import Dataflow.
Import ListNotations.

Section GridGraph.

  Definition Node : Type := list nat.
  Definition Dimensions : Type := list nat.

  Variable dims : Dimensions.

  Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
    match l1, l2 with
    | [], [] => true
    | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
    | _, _ => false
    end.

  Lemma list_eqb_spec {A : Type}
      (eqb : A -> A -> bool)
      (eqb_spec : forall x y : A, BoolSpec (x = y) (x <> y) (eqb x y))
      (l1 l2 : list A) : BoolSpec (l1 = l2) (l1 <> l2) (list_eqb eqb l1 l2).
  Proof.
    revert l2.
    induction l1 as [|x xs IH]; intros [|y ys]; simpl.
    - constructor. reflexivity.
    - constructor. discriminate.
    - constructor. discriminate.
    - destruct (eqb_spec x y) as [Hxy | Hxy].
      + subst y.
        destruct (IH ys) as [H | H].
        * subst ys. constructor. reflexivity.
        * constructor. intros Heq. inversion Heq. contradiction.
      + constructor. intros Heq. inversion Heq. contradiction.
  Qed.

  Definition node_eqb (n1 n2 : Node) : bool := list_eqb Nat.eqb n1 n2.

  Lemma node_eqb_spec :
    forall n1 n2 : Node,
      BoolSpec (n1 = n2) (n1 <> n2) (node_eqb n1 n2).
  Proof.
    unfold node_eqb.
    apply list_eqb_spec.
    intros x y. destruct (Nat.eqb_spec x y); constructor; congruence.
  Qed.

  Definition check_node_in_bounds (n : Node) : bool :=
    let fix check_dims coords dims :=
        match coords, dims with
        | [], [] => true
        | c :: cs, d :: ds => (c <? d) && check_dims cs ds
        | _, _ => false
        end
    in check_dims n dims.

  Inductive is_graph_node : Dimensions -> Node -> Prop :=
  | valid_nil : is_graph_node [] []
  | valid_cons : forall (d : nat) (ds : list nat) (coord : nat) (rest : Node),
      coord < d ->
      is_graph_node ds rest ->
      is_graph_node (d :: ds) (coord :: rest).

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

  Fixpoint all_nodes_h (dims : list nat) : list Node :=
    match dims with
    | [] => [[]]
    | d :: ds =>
        let rest := all_nodes_h ds in
        flat_map (fun i => map (fun r => i :: r) rest) (seq 0 d)
    end.
  
  Definition all_nodes : list Node := all_nodes_h dims.

  Theorem all_nodes_h_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes_h dims).
  Proof.
    intros n. split.
    - intros Hnode.
      induction Hnode.
      + simpl. left. reflexivity.
      + simpl. 
        remember (all_nodes_h ds) as rest_nodes. admit.
    - intros Hin.
      induction dims.
      + simpl in Hin. destruct Hin as [Heq | Hnil].
        * subst. constructor.
        * inversion Hnil.
  Admitted.

  Theorem all_nodes_correct : forall (n : Node),
    is_graph_node dims n <-> In n (all_nodes).
  Proof.
    intros n. unfold all_nodes.
    apply all_nodes_h_correct.
  Qed.


  (* Definition visit_graph_nodes (f : Node -> unit) : unit :=
  List.iter (fun n => if check_node_in_bounds n then f n else tt) (all_nodes dims).
 *)


End GridGraph.



