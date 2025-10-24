From Stdlib Require Import Lists.List.
From Stdlib Require Import Lists.ListSet.
From DatalogRocq Require Import ComputeCore.
From Datalog Require Import Datalog.

Import ListNotations.

(* Adjacency List Concrete Representation, plan to generalize later probably? *)
Definition dataflow_graph := list (core_id * core_set).

Definition valid_graph (g: dataflow_graph) : Prop :=
  NoDup (map fst g).

Fixpoint get_outgoing_edges (g: dataflow_graph) (c: core_id) : core_set :=
  match g with
  | [] => empty_core_set
  | (c', edges)::g' => if c =c c' then edges else get_outgoing_edges g' c
  end.

Fixpoint get_incoming_edges (g: dataflow_graph) (c: core_id) : core_set :=
  match g with
  | [] => empty_core_set
  | (c', edges)::g' => let inc_edges := get_incoming_edges g' c in
                if core_set_mem c edges then
                  core_set_add c' inc_edges
                else inc_edges
  end.

Definition get_cores (g: dataflow_graph) : core_set :=
  fold_right (fun (ce: core_id * core_set) acc =>
                let (c', edges) := ce in
                core_set_add c' acc)
             empty_core_set g.

Definition has_edge (g: dataflow_graph) (c1 c2: core_id) : bool :=
  core_set_mem c2 (get_outgoing_edges g c1).

Definition reachable (g: dataflow_graph) (c1 c2: core_id) : Prop :=
  exists path, path <> [] /\
               hd_error path = Some c1 /\
               last path c1 = c2 /\
               (forall i, i + 1 < length path -> has_edge g (nth i path c1) (nth (i + 1) path c1) = true).

Definition is_strongly_connected (g: dataflow_graph) : Prop :=
  forall c1 c2, In c1 (get_cores g) -> In c2 (get_cores g) -> reachable g c1 c2.

Definition latency := nat.

(* Latency should be defined for all cores reachable by each other in the dataflow graph *)
Definition latency_fn := core_id -> core_id -> option latency.

Definition valid_latency (g: dataflow_graph) (lat: latency_fn) : Prop :=
  forall c1 c2, reachable g c1 c2 -> exists l, lat c1 c2 = Some l.

Record dataflow_network := 
  {
    df_graph: dataflow_graph;
    df_latency: latency_fn
  }.

Definition get_latency (network: dataflow_network) (c1 c2: core_id) : option latency :=
  network.(df_latency) c1 c2.

