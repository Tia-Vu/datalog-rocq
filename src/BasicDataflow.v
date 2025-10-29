From DatalogRocq Require Import Dataflow.
From DatalogRocq Require Import ComputeCore.
From DatalogRocq Require Import Layout.
From Stdlib Require Import ZArith.
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Import ListNotations.

(* This file defines a basic 2D n x m grid data flow network. We define bidirectional
edges between all neighbors, and thus the network is strongly connected.
The latency between any two edges in the grid is defined to be the manhattan distance
between any two cores. *)

Notation "x <? y" := (Nat.ltb x y) (at level 70).

(* Core ids are numbers and they map to the 2d grid with math *)

Definition core_id_to_coords (c : core_id) (n m : nat) : nat * nat :=
  let x := c mod m in
  let y := c / m in
  (x, y).

Definition coords_to_core_id (x y : nat) (m : nat) : core_id :=
  y * m + x.

Definition in_bounds (x y: nat) (n m : nat) : bool :=
  andb (x <? m) (y <? n).

Definition valid_grid (n m : nat) : Prop :=
  n > 0 /\ m > 0.

Definition valid_core_id (c n m : nat) : Prop :=
  c < n * m.

(* Prove that converting from core_id to coordinates and back is the identity function *)
Lemma core_id_translate_roundtrip (x y n m : nat) :
  in_bounds x y n m = true ->
  valid_grid n m ->
  let (x', y') := core_id_to_coords (coords_to_core_id x y m) n m in
  x' = x /\ y' = y.
Proof.
  intros Hin Hvalid.
  unfold coords_to_core_id, core_id_to_coords in *.
  unfold in_bounds in Hin.
  apply andb_true_iff in Hin.
  destruct Hin as [Hx Hy].
  apply Nat.ltb_lt in Hx. 
  apply Nat.ltb_lt in Hy.
  split.
  - (* (y * m + x) mod m = x *)
    rewrite Nat.Div0.add_mod by lia.
    rewrite Nat.Div0.mod_mul by lia.
    rewrite Nat.add_0_l.
    unfold valid_grid in Hvalid. destruct Hvalid as [_ Hm].
    rewrite Nat.mod_small by (apply Nat.mod_upper_bound; lia).
    rewrite Nat.mod_small by assumption; auto.
  - (* (y * m + x) / m = y *)
    rewrite Nat.div_add_l by lia.
    rewrite Nat.div_small; [|assumption].
    lia.
Qed.

Lemma core_id_to_coords_inbounds (c n m : nat) :
  valid_grid n m ->
  valid_core_id c n m ->
  let (x, y) := core_id_to_coords c n m in
  in_bounds x y n m = true.
Proof.
   intros Hvalid Hcore.
   unfold core_id_to_coords, in_bounds.
   unfold valid_core_id in Hcore.
   unfold valid_grid in Hvalid. destruct Hvalid as [Hn Hm].
   apply andb_true_iff. split.
   - apply Nat.ltb_lt. apply Nat.mod_upper_bound. lia.
  - apply Nat.ltb_lt. apply Nat.Div0.div_lt_upper_bound; lia.
Qed. 

(* Prove the other direction *)

Lemma coords_translate_roundtrip (c n m : nat) :
  valid_grid n m ->
  let (x, y) := core_id_to_coords c n m in
  coords_to_core_id x y m = c.
Proof.
  intros Hvalid.
  unfold core_id_to_coords, coords_to_core_id.
  unfold valid_grid in Hvalid.
  destruct Hvalid as [_ Hm].
  replace (c / m * m) with (m * (c / m)) by lia.
  symmetry.
  apply Nat.div_mod.
  lia.
Qed.

Definition manhattan_distance (n m : nat) (c1 c2 : core_id) : Z :=
  let (x1, y1) := core_id_to_coords c1 n m in
  let (x2, y2) := core_id_to_coords c2 n m in
  Z.abs (Z.of_nat x1 - Z.of_nat x2) + Z.abs (Z.of_nat y1 - Z.of_nat y2).

Definition latency (n m : nat) (c1 c2 : core_id) : Z :=
  manhattan_distance n m c1 c2.

Definition get_neighbors_coords (x y n m : nat) : list (nat * nat) :=
  let candidates := [(x+1, y); (x-1, y); (x, y+1); (x, y-1)] in
  filter (fun '(x', y') => in_bounds x' y' n m)
  candidates.

Definition get_neighbors_core_ids (c : core_id) (n m : nat) : list core_id :=
  let (x, y) := core_id_to_coords c n m in
  let coords := get_neighbors_coords x y n m in
  map (fun '(x', y') => coords_to_core_id x' y' m) coords.

Definition in_bounds_pair (p : nat * nat) (n m : nat) : bool :=
  let (x, y) := p in
  in_bounds x y n m.

Lemma Forall_filter {A} (P : A -> bool) (l : list A) :
  Forall (fun x => P x = true) (filter P l).
Proof.
  induction l as [|x xs IH]; simpl.
  - constructor.
  - destruct (P x) eqn:Hx.
    + constructor; auto.
    + apply IH.
Qed.

Lemma get_neighbors_coords_in_bounds (x y n m : nat) :
  valid_grid n m ->
  in_bounds x y n m = true ->
  Forall (fun p => in_bounds_pair p n m = true)
         (get_neighbors_coords x y n m).
Proof.
  intros Hvalid Hxy.
  unfold get_neighbors_coords.
  apply Forall_filter.
Qed.

Definition list_to_core_set (l : list core_id) : core_set :=
  fold_right core_set_add empty_core_set l.

Definition basic_dataflow_graph (n m : nat) : dataflow_graph :=
  let all_core_ids := seq 0 (n * m) in
  map (fun c =>
         let neighbors := get_neighbors_core_ids c n m in
         (c, list_to_core_set neighbors))
      all_core_ids.

Definition basic_dataflow_network (n m : nat) : dataflow_network :=
  {|
    df_graph := basic_dataflow_graph n m;
    df_latency := fun c1 c2 =>
      if has_edge (basic_dataflow_graph n m) c1 c2 then
        Some (Z.to_nat (latency n m c1 c2))
      else None
  |}.

