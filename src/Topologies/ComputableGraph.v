From coqutil Require Import Map.Interface Eqb.
From Stdlib Require Import List Lia PeanoNat.
From DatalogRocq Require Import Topologies.Graph.
Import ListNotations.

Section ComputableGraph.
Context {Node : Type}.
Context {node_eqb : Eqb Node} {node_eqb_ok : Eqb_ok node_eqb}.
Context {node_set : map.map Node unit} {node_set_ok : map.ok node_set}.
Context {edge_set : map.map Node node_set} {edge_set_ok : map.ok edge_set}.

Record ComputableGraph := {
  nodes : node_set;
  edges : edge_set
}.

Definition check_node_valid (n : Node) (ns : node_set) : bool :=
  match map.get ns n with
  | Some _ => true
  | None => false
  end.

Definition check_edge_valid (n1 n2 : Node) (ns : node_set) : bool :=
  check_node_valid n1 ns && check_node_valid n2 ns.

(* Check all edges only use nodes from the node set *)
Definition check_edges_valid (es : edge_set) (ns : node_set) : bool :=
  map.forallb (fun n1 neighbors =>
    map.forallb (fun n2 _ =>
      check_edge_valid n1 n2 ns
    ) neighbors
  ) es.

Definition check_graph_valid (cg : ComputableGraph) : bool :=
  check_edges_valid cg.(edges) cg.(nodes).

Definition cg_nodes_to_g_nodes (ns : node_set) : Node -> Prop :=
  fun n => check_node_valid n ns = true.

Definition check_edge_exists (n1 n2 : Node) (es : edge_set) : bool :=
  match map.get es n1 with
  | Some neighbors => match map.get neighbors n2 with
                      | Some _ => true
                      | None => false
                      end
  | None => false
  end.

Definition cg_edges_to_g_edges (es : edge_set) (ns : node_set) : Node -> Node -> Prop :=
  fun n1 n2 => check_edge_exists n1 n2 es = true.

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
  intros cg.
  unfold check_graph_valid, check_edges_valid, good_graph, computable_graph_to_graph. simpl.
  unfold check_edges_valid.
  rewrite forallb_spec.
  split.
  - intros H n1 n2 Hedge.
    (* Hedge : check_edge_exists n1 n2 cg.(edges) = true *)
    unfold check_edge_exists in Hedge.
    destruct (map.get cg.(edges) n1) eqn:E1; try discriminate.
    destruct (map.get r n2) eqn:E2; try discriminate.
    specialize (H n1 r E1).
    rewrite forallb_spec in H.
    specialize (H n2 u E2).
    unfold check_edge_valid in H.
    apply andb_prop in H. destruct H as [Hn1 Hn2].
    split; assumption.
  - intros H n1 neighbors Hn1.
    rewrite forallb_spec.
    intros n2 u Hn2.
    unfold check_edge_valid.
    apply andb_true_intro.
    assert (Hedge : check_edge_exists n1 n2 cg.(edges) = true).
    { unfold check_edge_exists. rewrite Hn1, Hn2. reflexivity. }
    apply H in Hedge.
    destruct Hedge as [Hn1valid Hn2valid].
    split; assumption.
Qed.

Definition cg_neighbors (g : ComputableGraph) (n : Node) : node_set :=
  match map.get g.(edges) n with
  | Some ns => ns
  | None => map.empty
  end.

Record bfs_state := {
  bs_queue : list (Node * list Node);
  bs_visited : node_set;
}.

Definition bfs_initial (start : Node) : bfs_state :=
  {|
    bs_queue := [(start, [start])];
    bs_visited := map.put map.empty start tt;
  |}.

Definition bfs_step (g : ComputableGraph) (target : Node) (state : bfs_state)
    : bfs_state + list Node :=
  match state.(bs_queue) with
  | [] => inl state
  | (node, path) :: rest =>
    if node_eqb node target then inr (List.rev path)
    else
      let neighbor_set := cg_neighbors g node in
      let '(unvisited, new_visited) :=
        map.fold (fun '(uvs, vis) n _ =>
          match map.get vis n with
          | Some _ => (uvs, vis)
          | None => (n :: uvs, map.put vis n tt)
          end) ([], state.(bs_visited)) neighbor_set in
      let new_entries := List.map (fun n => (n, n :: path)) unvisited in
      inl {|
        bs_queue := rest ++ new_entries;
        bs_visited := new_visited;
      |}
  end.

Fixpoint bfs_aux (g : ComputableGraph) (target : Node) (state : bfs_state) (fuel : nat)
    : option (list Node) :=
  match fuel with
  | O => None
  | S fuel' =>
    match bfs_step g target state with
    | inr path => Some path
    | inl state' =>
      match state'.(bs_queue) with
      | [] => None
      | _ => bfs_aux g target state' fuel'
      end
    end
  end.

Definition msize (m : node_set) : nat := map.fold (fun n _ _ => S n) 0 m.

Definition graph_fuel (g : ComputableGraph) : nat := msize g.(nodes).

Definition bfs (g : ComputableGraph) (start target : Node) : option (list Node) :=
  bfs_aux g target (bfs_initial start) (graph_fuel g).

Definition get_path (g : ComputableGraph) (nstart nend : Node) : option (list Node) :=
  bfs g nstart nend.

(*============================================================================*)
(*  get_path soundness: a returned path is a real edge-walk start -> end       *)
(*============================================================================*)

(* an edge of the computable graph *)
Definition cg_edge (g : ComputableGraph) (n1 n2 : Node) : Prop :=
  check_edge_exists n1 n2 g.(edges) = true.

(* [l] is a walk: every adjacent pair is an edge *)
Definition edge_walk (g : ComputableGraph) (l : list Node) : Prop :=
  forall i a b, nth_error l i = Some a -> nth_error l (S i) = Some b -> cg_edge g a b.

(* [path] is a real path from [s] to [e] (head = s, last = e, all adjacent pairs edges) *)
Definition is_path (g : ComputableGraph) (s e : Node) (path : list Node) : Prop :=
  path <> [] /\ nth_error path 0 = Some s /\
  nth_error path (pred (length path)) = Some e /\ edge_walk g path.

Lemma edge_walk_snoc (g : ComputableGraph) (l : list Node) (x : Node) :
  edge_walk g l ->
  (forall a, nth_error l (pred (length l)) = Some a -> cg_edge g a x) ->
  edge_walk g (l ++ [x]).
Proof.
  intros Hw Hlast i a b Hi HSi.
  assert (HSb : nth_error (l ++ [x]) (S i) <> None) by congruence.
  apply nth_error_Some in HSb. rewrite length_app in HSb. cbn [length] in HSb.
  destruct (Nat.eqb_spec (S i) (length l)) as [HSeq | HSne].
  - rewrite nth_error_app1 in Hi by lia.
    assert (Hi' : nth_error l (pred (length l)) = Some a) by (rewrite <- HSeq; cbn; exact Hi).
    rewrite HSeq, nth_error_app2 in HSi by lia.
    rewrite Nat.sub_diag in HSi. cbn in HSi. injection HSi as <-.
    apply Hlast. exact Hi'.
  - rewrite nth_error_app1 in Hi by lia. rewrite nth_error_app1 in HSi by lia.
    exact (Hw i a b Hi HSi).
Qed.

(* a neighbor key really is an edge target *)
Lemma cg_neighbors_edge (g : ComputableGraph) (node n : Node) (v : unit) :
  map.get (cg_neighbors g node) n = Some v -> cg_edge g node n.
Proof.
  unfold cg_neighbors, cg_edge, check_edge_exists. intros H.
  destruct (map.get g.(edges) node) as [ns|] eqn:E.
  - rewrite H. reflexivity.
  - rewrite map.get_empty in H. discriminate.
Qed.

(* the unvisited list of the neighbor-fold (exactly [bfs_step]'s) only contains neighbor keys *)
Lemma fold_unvisited_keys (neighbors vis0 : node_set) (n : Node) :
  In n (fst (map.fold (fun '(uvs, vis) k _ =>
              match map.get vis k with
              | Some _ => (uvs, vis)
              | None => (k :: uvs, map.put vis k tt)
              end) ([], vis0) neighbors)) ->
  exists v, map.get neighbors n = Some v.
Proof.
  revert n.
  apply (map.fold_spec
    (fun (m : node_set) (acc : list Node * node_set) =>
       forall n, In n (fst acc) -> exists v, map.get m n = Some v)).
  - intros n H. destruct H.
  - intros k v m acc Hmk IH n H.
    destruct acc as [uvs vis]. cbn [fst] in IH.
    destruct (map.get vis k) eqn:E; cbn [fst] in H.
    + destruct (IH n H) as [v' Hv']. exists v'.
      rewrite map.get_put_diff; [exact Hv'|]. intro; subst; congruence.
    + destruct H as [-> | H].
      * exists v. apply map.get_put_same.
      * destruct (eqb_boolspec _ n k) as [->|Hne].
        -- exists v. apply map.get_put_same.
        -- destruct (IH n H) as [v' Hv']. exists v'.
           rewrite map.get_put_diff by exact Hne. exact Hv'.
Qed.

(* the BFS invariant: every queue entry [(node, p)] has [rev p] a real path [start -> node] *)
Definition good_entry (g : ComputableGraph) (s : Node) (e : Node * list Node) : Prop :=
  is_path g s (fst e) (List.rev (snd e)).

Lemma good_entry_initial (g : ComputableGraph) (s : Node) :
  good_entry g s (s, [s]).
Proof.
  unfold good_entry, is_path. cbn. repeat split; try discriminate.
  intros i a b Hi Hib. destruct i; cbn in *; [discriminate | destruct i; discriminate].
Qed.

(* extending a real path [s -> node] by an edge [node -> n] gives a real path [s -> n] *)
Lemma is_path_snoc (g : ComputableGraph) (s node n : Node) (p : list Node) :
  is_path g s node p -> cg_edge g node n -> is_path g s n (p ++ [n]).
Proof.
  intros [Hne [Hhd [Hlast Hwalk]]] Hedge. unfold is_path. repeat split.
  - intro Hc. apply app_eq_nil in Hc. destruct Hc; discriminate.
  - rewrite nth_error_app1; [exact Hhd|]. destruct p; [contradiction | cbn; lia].
  - rewrite length_app. cbn [length].
    replace (pred (length p + 1)) with (length p) by lia.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - apply edge_walk_snoc; [exact Hwalk|]. intros a Ha. rewrite Hlast in Ha.
    injection Ha as <-. exact Hedge.
Qed.

(* one BFS step preserves the invariant on the queue, and any returned path is a real path *)
Lemma bfs_step_good (g : ComputableGraph) (s target : Node) (state : bfs_state) :
  Forall (good_entry g s) (bs_queue state) ->
  match bfs_step g target state with
  | inr path => is_path g s target path
  | inl state' => Forall (good_entry g s) (bs_queue state')
  end.
Proof.
  intros HF. unfold bfs_step.
  destruct (bs_queue state) as [|[node p] rest] eqn:Hq.
  - rewrite Hq. constructor.
  - inversion HF as [|x l Hhead Htail]; subst.
    pose proof (node_eqb_ok node target) as Hb. cbv [eqb] in Hb.
    destruct (node_eqb node target).
    + subst. exact Hhead.
    + destruct (map.fold (fun '(uvs, vis) n _ =>
          match map.get vis n with
          | Some _ => (uvs, vis)
          | None => (n :: uvs, map.put vis n tt)
          end) ([], state.(bs_visited)) (cg_neighbors g node)) as [unvisited new_visited] eqn:Hfold.
      cbn. apply Forall_app. split; [exact Htail|].
      apply Forall_map. apply Forall_forall. intros n Hn_in.
      assert (Hnb : exists v, map.get (cg_neighbors g node) n = Some v).
      { apply (fold_unvisited_keys (cg_neighbors g node) (bs_visited state) n).
        rewrite Hfold. cbn [fst]. exact Hn_in. }
      destruct Hnb as [v Hv].
      unfold good_entry in *. cbn [fst snd] in *.
      replace (List.rev (n :: p)) with (List.rev p ++ [n]) by reflexivity.
      apply (is_path_snoc g s node n (List.rev p)); [exact Hhead|].
      eapply cg_neighbors_edge; exact Hv.
Qed.

Lemma bfs_aux_sound (g : ComputableGraph) (s target : Node) :
  forall fuel state path,
  Forall (good_entry g s) (bs_queue state) ->
  bfs_aux g target state fuel = Some path ->
  is_path g s target path.
Proof.
  induction fuel as [|fuel IH]; intros state path HF Haux; cbn in Haux; [discriminate|].
  pose proof (bfs_step_good g s target state HF) as Hstep.
  destruct (bfs_step g target state) as [state'|path0] eqn:Hbs.
  - destruct (bs_queue state') as [|e q] eqn:Hq'; [discriminate|].
    apply (IH state' path); [rewrite Hq'; exact Hstep | exact Haux].
  - injection Haux as <-. exact Hstep.
Qed.

(* MAIN: a path returned by [get_path] is a real edge-path from [nstart] to [nend]. *)
Theorem get_path_spec (g : ComputableGraph) (nstart nend : Node) (path : list Node) :
  get_path g nstart nend = Some path -> is_path g nstart nend path.
Proof.
  unfold get_path, bfs. intros H.
  eapply bfs_aux_sound; [|exact H].
  unfold bfs_initial. cbn. constructor; [apply good_entry_initial | constructor].
Qed.

End ComputableGraph.
Arguments ComputableGraph _ {_ _}.
