(* GridTopology: the *topology* backend for the compiler -- node ids and the grid graph.
   This is entirely independent of the datalog program types (relations/variables/functions):
   it only fixes what a node identifier is and how to build a grid topology graph from
   dimensions.  Combine it with a datalog backend (e.g. StringDatalog) to get a concrete
   compiler.

   Node ids are grid coordinates represented as [list nat] -- exactly [GridGraph.Node] -- so the
   grid connectivity proofs apply directly,
   with no extra encoding.  This works for grids of any dimension, not just 2D. *)

From Stdlib Require Import List ZArith.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridGraph SortedListList SortedListNat ComputableGraph.
From coqutil Require Import Map.Interface Eqb Decidable Datatypes.List.
From GraphSearch Require Import GraphInterface GraphImpl.
Import ListNotations.

(* Build the grid topology graph (node set + neighbor edges) from dimensions.  Since a node id
   *is* its coordinate list, there is no destructuring/reassembly. *)
Definition build_topo_node_set (dims : GridGraph.Dimensions) : @map.rep Node unit _ :=
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
