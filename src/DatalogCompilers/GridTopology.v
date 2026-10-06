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
From coqutil Require Import Map.Interface.
From Datalog.Util Require Import Map.
Import ListNotations.

(* Build the grid topology graph (node set + neighbor edges) from dimensions.  Since a node id
   *is* its coordinate list, there is no destructuring/reassembly. *)
Definition build_topo_node_set (dims : GridGraph.Dimensions) : partial_map Node unit :=
  List.fold_left
    (fun acc n => map.put acc n tt)
    (GridGraph.all_nodes_h dims)
    map.empty.

Definition build_topo_edge_set (dims : GridGraph.Dimensions)
    : partial_map Node (partial_map Node unit) :=
  let nodes := GridGraph.all_nodes_h dims in
  List.fold_left
    (fun acc n =>
      let neighbors :=
        List.filter (fun n2 => GridGraph.is_neighbor dims n n2) nodes in
      let neighbor_map :=
        List.fold_left (fun m nb => map.put m nb tt) neighbors map.empty in
      map.put acc n neighbor_map)
    nodes map.empty.

Definition make_topo_graph (dims : GridGraph.Dimensions) : ComputableGraph Node :=
  {| nodes := build_topo_node_set dims;
     edges := build_topo_edge_set dims |}.
