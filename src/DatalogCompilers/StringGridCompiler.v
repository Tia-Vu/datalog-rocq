(* StringGridCompiler: a concrete compiler for string-datalog programs laid out on a 2D grid.
   It is just the composition of two independent backends:
     - StringDatalog  : the datalog program representation (string relations/variables/functions),
     - GridTopology   : the node-id type and grid topology graph.
   Given a program and an (indexed) layout it compiles end to end. *)

From Stdlib Require Import List ZArith String.
From Datalog Require Import Datalog NattifyRel RelMap.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler GridTopology StringDatalog StringDatalogParams
  GridGraph SortedListNat SortedListList SortedListPair DistributedHardwareProgram.
From coqutil Require Import Map.Interface Map.SortedListString Result.
Import ListNotations.
Import StringDatalogParams.

Notation node_id     := GridGraph.Node.


(* [make_layout_map program layout] : a [node -> rules] map from an indexed layout
   (a list of [(node_id, rule_index_list)] pairs over the [program]). *)
Definition make_layout_map
    (program : list rule)
    (layout  : list (node_id * list nat))
    : @map.rep node_id (list rule) _ :=
  List.fold_left
    (fun acc '(nid, idxs) =>
      let empty_rule := normal_rule [] [] in
      let rules := List.map (fun i => List.nth i program empty_rule) idxs in
      map.put acc nid rules)
    layout map.empty.

(* [compile] now consumes an already-numbered ([rel_id]) program, so the string relations are
   nattified here first (via [NattifyRel.encode_rel] over the program's own relations -- matching
   [nattify_and_compile_correct]'s [input_rels := program_rels p]). *)
Definition rel_ids (program : list rule) : string -> rel_id :=
  encode_rel (List.flat_map Datalog.all_rels program) program.

Definition nattify_layout (enc : string -> rel_id)
    (slayout : @map.rep node_id (list rule) _) : @map.rep node_id (list HardwareProgram.lowered_rule) _ :=
  map.fold (fun acc nid rules => map.put acc nid (List.map (map_rule_rels enc) rules)) map.empty slayout.

Definition nattify_fact_locs (enc : string -> rel_id) (fl : @map.rep string (list node_id) _) : @map.rep rel_id (list node_id) _ :=
  map.fold (fun acc R locs => map.put acc (enc R) locs) map.empty fl.

(* The end-to-end compiler: nattify the string layout / fact-locations, then wire the numbered
   program and the grid topology into the fuel-free [compile] (which computes the routing fuel
   = #grid-nodes itself). *)
Definition compile_program
    (program        : list rule)
    (layout         : list (node_id * list nat))
    (fact_producers : @map.rep string (list node_id) _)
    (fact_consumers : @map.rep string (list node_id) _)
    (topo_dims      : GridGraph.Dimensions)
    : _ :=
  let enc := rel_ids program in
  compile_with_dumb_ftables
    (nattify_layout enc (make_layout_map program layout))
    (nattify_fact_locs enc fact_producers) (nattify_fact_locs enc fact_consumers)
    (GridTopology.make_topo_graph topo_dims).

(* The rel-name <-> rel-id table the frontend assigns (via [NattifyRel]'s [rel_table] / [encode_rel]),
   exposed for tooling that needs to relate a fact keyed by relation name to the compiled program's
   numeric [output_rel]/[trel] ids -- e.g. a human-authored/random input-fact workload. *)
Definition compile_program_rel_ids (program : list rule) : list (string * rel_id) :=
  let enc := rel_ids program in
  List.map (fun R => (R, enc R)) (rel_table (List.flat_map Datalog.all_rels program) program).

(* PLACEHOLDER fact-locations: make EVERY grid node an input AND output node for EVERY relation
   appearing in [program].  Useful for examples that have not (yet) designated real input/output
   nodes, so they still satisfy the compiler's input/output routing gates.
   TODO: replace with the real input (fact-producer) and output (fact-consumer) nodes for the
   program -- only the genuine EDB sources and result sinks, not every node. *)
Definition all_io_locations (program : list rule) (layout : list (node_id * list nat))
    (topo_dims : GridGraph.Dimensions) : @map.rep string (list node_id) _ :=
  let nodes := GridGraph.all_nodes_h topo_dims in
  (* only relations of the rules the layout actually assigns are in the global context *)
  let assigned := List.flat_map (fun '(_, idxs) =>
                    List.map (fun i => List.nth i program (Datalog.normal_rule [] [])) idxs) layout in
  map.of_list (List.map (fun R => (R, nodes))
           (List.nodup String.string_dec (List.flat_map Datalog.all_rels assigned))).
