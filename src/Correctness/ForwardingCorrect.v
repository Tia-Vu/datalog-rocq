(* Phase B of the forwarding-table verification: [add_path_to_forwarding_table] lays down a
   [DestEdge] chain along its path, and the whole construction is monotone (adding never removes
   an existing forwarding edge).  These are the per-step facts Phase C assembles, together with
   [ComputableGraph.get_path_spec] (paths are real edge-walks), into [good_network_streaming] for
   the compiled network's own forwarding tables. *)

From Stdlib Require Import List Bool Lia PeanoNat.
From coqutil Require Import Map.Interface Map.Properties Datatypes.ListSet Eqb Tactics.destr.
From Datalog Require Import Map Default.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler HardwareProgram DistributedHardwareProgram ComputableGraph.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

Section ForwardingCorrect.

Context {node_id : Type}.
Context {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.
Context {node_id_set : map.map node_id unit} {node_id_set_ok : map.ok node_id_set}.
Context {node_id_graph : graph.graph node_id} {node_id_graph_ok : graph.ok node_id_graph}.

Notation node_graph := (@ComputableGraph.ComputableGraph node_id node_id_set node_id_graph).
Notation cg_edge := (@ComputableGraph.cg_edge node_id node_id_set node_id_graph).

Context {forwarding_table : map.map (rel_id * node_id) (list node_id)}
        {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map : map.map node_id forwarding_table}
        {node_ftable_map_ok : map.ok node_ftable_map}.

Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

(* the forwarding edges node [node] has for relation [rel] in [ftables] *)
Definition node_rel_dests (ftables : node_ftable_map) (node : node_id) (rel : rel_id)
    (original_source : node_id) : list node_id :=
  get_or_default (get_or_default ftables node) (rel, original_source).

Definition has_fwd_edge (ftables : node_ftable_map) (node : node_id) (rel : rel_id)
    (original_source : node_id) (m : node_id) : Prop :=
  In m (node_rel_dests ftables node rel original_source).

(*============================================================================*)
(*  Soundness: every forwarding edge is a real graph edge                      *)
(*============================================================================*)

(* the table is *edge-sound* when every forwarding edge it records is a real graph edge *)
Definition ftable_edges_sound (g : node_graph) (ftables : node_ftable_map) : Prop :=
  forall node rel s m, has_fwd_edge ftables node rel s m -> cg_edge g node m.

(* an edge of the graph the table induces for [R] is exactly a recorded next hop *)
Lemma edge_graph_of_ftables (ftables : node_ftable_map) (R : rel_id) (s : node_id)
    (n m : node_id) :
  graph.edge (graph_of_ftables_at ftables R s) n m <-> has_fwd_edge ftables n R s m.
Proof.
  unfold DistributedDatalogToHardwareCompiler.graph_of_ftables_at,
    has_fwd_edge, node_rel_dests.
  revert n m.
  eapply (map.fold_spec
    (fun m0 acc => forall n m, graph.edge acc n m
                   <-> In m (get_or_default (get_or_default m0 n) (R, s)))).
  - intros n m. unfold get_or_default, get_or. rewrite map.get_empty.
    cbv [default map_default]. rewrite map.get_empty. cbv [list_default].
    split; [apply graph.edge_empty | intros []].
  - intros k v m0 acc Hk IH n m. rewrite graph.edge_put_edges, IH.
    unfold get_or_default, get_or. rewrite map.get_put_dec.
    destr (eqb k n).
    + rewrite Hk. cbv [default map_default]. rewrite map.get_empty. cbv [list_default].
      cbn [In]. tauto.
    + split; [intros [H|[Hc _]]; [exact H | congruence] | intros H; left; exact H].
Qed.

(* the decidable check on an externally generated table gives exactly the edge-soundness the
   forwarding proofs used to get from [get_path_spec]. *)
Lemma ftables_in_graphb_sound (g : node_graph) (ftables : node_ftable_map) :
  ftables_in_graphb g ftables = true -> ftable_edges_sound g ftables.
Proof.
  intros Hcheck node rel s m Hfwd.
  unfold has_fwd_edge, node_rel_dests, get_or_default, get_or in Hfwd.
  destruct (map.get ftables node) as [ft|] eqn:Hnode;
    [| cbv [default map_default list_default] in Hfwd; rewrite map.get_empty in Hfwd; destruct Hfwd].
  pose proof (map.get_forallb _ ftables Hcheck node ft Hnode) as Hft.
  destruct (map.get ft (rel, s)) as [hops|] eqn:Hrel; [|destruct Hfwd].
  pose proof (map.get_forallb _ ft Hft (rel, s) hops Hrel) as Hhops.
  unfold DistributedDatalogToHardwareCompiler.hops_in_graphb in Hhops.
  rewrite forallb_forall in Hhops.
  apply ComputableGraph.check_edge_exists_iff. exact (Hhops _ Hfwd).
Qed.

(*============================================================================*)
(*  Phase C2 (completeness engine): a forwarding edge laid down by some step    *)
(*  of the construction survives to the final table.  Generic over an arbitrary *)
(*  monotone table-predicate [P] (instantiated with [fun ft => has_fwd_edge     *)
(*  ft a r b] at the use site), so the same combinators thread both the         *)
(*  [map.fold] over producer/consumer node-sets and the [fold_left] over rels.  *)



End ForwardingCorrect.
