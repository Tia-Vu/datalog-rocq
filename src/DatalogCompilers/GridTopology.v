(* GridTopology: the *topology* backend for the compiler -- node ids and the grid graph.
   This is entirely independent of the datalog program types (relations/variables/functions):
   it only fixes what a node identifier is and how to build a grid topology graph from
   dimensions.  Combine it with a datalog backend (e.g. StringDatalog) to get a concrete
   compiler.

   Node ids are grid coordinates represented as [list nat] -- exactly [GridGraph.Node] -- so the
   grid connectivity proofs apply directly,
   with no extra encoding.  This works for grids of any dimension, not just 2D. *)

From Stdlib Require Import List ZArith.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridGraph MapInstances SortedListInj ComputableGraph.
From coqutil Require Import Map.Interface Eqb Decidable Datatypes.List.
From Datalog.Util Require Import Map.
From GraphSearch Require Import GraphInterface GraphImpl.
Import ListNotations.

(* Build the grid topology graph (node set + neighbor edges) from dimensions.  Since a node id
   *is* its coordinate list, there is no destructuring/reassembly. *)
Definition build_topo_node_set (dims : GridGraph.Dimensions) : partial_map Node unit :=
  List.fold_left
    (fun acc n => map.put acc n tt)
    (GridGraph.all_nodes_h dims)
    map.empty.

Definition build_topo_edges (dims : GridGraph.Dimensions) : @graph.rep Node _ :=
  let nodes := GridGraph.all_nodes_h dims in
  List.fold_left
    (fun acc n =>
      graph.put_edges acc n (List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes))
    nodes graph.empty.

Definition make_topo_graph (dims : GridGraph.Dimensions) : ComputableGraph Node :=
  {| ComputableGraph.nodes := build_topo_node_set dims;
     ComputableGraph.edges := build_topo_edges dims |}.

Definition encode_fwd_from (s : @fwd_from.fwd_from Node) : nat * (list nat * nat) :=
  match s with
  | fwd_from.input => (0, ([], 0))
  | fwd_from.self => (1, ([], 0))
  | fwd_from.node n ch => (2, (n, ch))
  end.

Lemma encode_fwd_from_inj (x y : @fwd_from.fwd_from Node) :
  encode_fwd_from x = encode_fwd_from y -> x = y.
Proof. destruct x, y; cbn; congruence. Qed.

#[export] Instance fwd_from_strict_order : SortedList.parameters.strict_order (SortedListInj.inj_order encode_fwd_from) :=
  SortedListInj.inj_strict_order encode_fwd_from encode_fwd_from_inj.

Definition encode_vnode (v : @vnode.vnode Node) : nat * (list nat * (nat * (list nat * nat))) :=
  match v with
  | vnode.fact_dst n => (0, (n, (0, ([], 0))))
  | vnode.at_port n src => (1, (n, encode_fwd_from src))
  | vnode.ext_input => (2, ([], (0, ([], 0))))
  | vnode.ext_output => (3, ([], (0, ([], 0))))
  end.

Lemma encode_vnode_inj (x y : @vnode.vnode Node) : encode_vnode x = encode_vnode y -> x = y.
Proof.
  destruct x, y; cbn; intros H; inversion H; subst; try reflexivity.
  f_equal. apply encode_fwd_from_inj. assumption.
Qed.

#[export] Instance vnode_strict_order : SortedList.parameters.strict_order (SortedListInj.inj_order encode_vnode) :=
  SortedListInj.inj_strict_order encode_vnode encode_vnode_inj.
