From coqutil Require Import Map.Interface Eqb.
From Stdlib Require Import List.
From DatalogRocq Require Import Topologies.Graph.
From GraphSearch Require Import GraphInterface.
Import ListNotations.

Section ComputableGraph.
Context {Node : Type}.
Context {node_eqb : Eqb Node} {node_eqb_ok : Eqb_ok node_eqb}.
Context {node_set : map.map Node unit} {node_set_ok : map.ok node_set}.
Context {graph : graph.graph Node} {graph_ok : graph.ok graph}.

Record ComputableGraph := {
  nodes : node_set;
  edges : graph
}.

Definition check_node_valid (n : Node) (ns : node_set) : bool :=
  match map.get ns n with
  | Some _ => true
  | None => false
  end.

Definition check_edge_valid (n1 n2 : Node) (ns : node_set) : bool :=
  check_node_valid n1 ns && check_node_valid n2 ns.

(* Check all edges only use nodes from the node set *)
Definition check_edges_valid (es : graph) (ns : node_set) : bool :=
  forallb (fun n1 => forallb (fun n2 => check_edge_valid n1 n2 ns) (graph.edges es n1))
    (graph.sources es).

Definition check_graph_valid (cg : ComputableGraph) : bool :=
  check_edges_valid cg.(edges) cg.(nodes).

Definition cg_nodes_to_g_nodes (ns : node_set) : Node -> Prop :=
  fun n => check_node_valid n ns = true.

Definition check_edge_exists (n1 n2 : Node) (es : graph) : bool :=
  existsb (eqb n2) (graph.edges es n1).

Definition cg_edges_to_g_edges (es : graph) (ns : node_set) : Node -> Node -> Prop :=
  fun n1 n2 => check_edge_exists n1 n2 es = true.

Lemma check_edge_exists_iff (es : graph) (n1 n2 : Node) :
  check_edge_exists n1 n2 es = true <-> graph.edge es n1 n2.
Proof.
  unfold check_edge_exists, graph.edge. rewrite existsb_exists. split.
  - intros [x [Hin Hx]]. destruct (eqb_boolspec _ n2 x) as [->|]; [exact Hin | discriminate].
  - intros Hin. exists n2. split; [exact Hin | destruct (eqb_boolspec _ n2 n2); congruence].
Qed.

(* an edge of the computable graph *)
Definition cg_edge (g : ComputableGraph) (n1 n2 : Node) : Prop :=
  graph.edge g.(edges) n1 n2.

Definition computable_graph_to_graph (cg : ComputableGraph) : Graph :=
  {|
    Graph.nodes := fun n => check_node_valid n cg.(nodes) = true;
    Graph.edge := fun n1 n2 => check_edge_exists n1 n2 cg.(edges) = true
  |}.

Lemma forallb_spec : forall {key val : Type} {keqb : Eqb key} {keqb_ok : Eqb_ok keqb}
    {m : map.map key val} {ok : map.ok m}
    (f : key -> val -> bool) (mp : m),
  map.forallb f mp = true <->
  forall k v, map.get mp k = Some v -> f k v = true.
Proof.
  intros. unfold map.forallb.
  eapply (map.fold_spec (fun mp r => r = true <-> forall k v, map.get mp k = Some v -> f k v = true)).
  - split.
    + intros _ k v. rewrite map.get_empty. discriminate.
    + intros. reflexivity.
  - intros k v m' r Hget [IHf IHb].
    split.
    + intros Handb k' v' Hget'.
      apply andb_prop in Handb. destruct Handb as [Hr Hf].
      destruct (eqb_boolspec _ k' k) as [->|Hne].
      * rewrite map.get_put_same in Hget'. inversion Hget'. subst. exact Hf.
      * rewrite map.get_put_diff in Hget' by exact Hne.
        exact (IHf Hr k' v' Hget').
    + intros Hall.
      apply andb_true_intro. split.
      * apply IHb. intros k' v' Hget'.
        apply Hall. rewrite map.get_put_diff; [exact Hget'|].
        intros ->. rewrite Hget in Hget'. discriminate.
      * apply Hall. rewrite map.get_put_same. reflexivity.
Qed.

Lemma check_graph_correct : forall cg,
  check_graph_valid cg = true <-> good_graph (computable_graph_to_graph cg).
Proof.
  intros cg. unfold check_graph_valid, check_edges_valid, good_graph,
    computable_graph_to_graph. cbn [Graph.nodes Graph.edge].
  setoid_rewrite check_edge_exists_iff.
  rewrite forallb_forall. split.
  - intros H n1 n2 Hedge.
    assert (Hsrc : In n1 (graph.sources cg.(edges)))
      by (apply graph.sources_spec; exists n2; exact Hedge).
    specialize (H n1 Hsrc). rewrite forallb_forall in H.
    specialize (H n2 Hedge). unfold check_edge_valid in H.
    apply andb_prop in H. exact H.
  - intros H n1 _. rewrite forallb_forall. intros n2 Hedge.
    unfold check_edge_valid. apply andb_true_intro. exact (H n1 n2 Hedge).
Qed.

End ComputableGraph.
Arguments ComputableGraph _ {_ _}.
