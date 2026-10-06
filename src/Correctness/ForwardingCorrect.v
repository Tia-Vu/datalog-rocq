(* Phase B of the forwarding-table verification: [add_path_to_forwarding_table] lays down a
   [DestEdge] chain along its path, and the whole construction is monotone (adding never removes
   an existing forwarding edge).  These are the per-step facts Phase C assembles, together with
   [ComputableGraph.get_path_spec] (paths are real edge-walks), into [good_network_streaming] for
   the compiled network's own forwarding tables. *)

From Stdlib Require Import List Bool Lia PeanoNat.
From coqutil Require Import Map.Interface Map.Properties Datatypes.List Datatypes.ListSet Eqb.
From Datalog.Util Require Import Map Default.
From DatalogRocq Require Import Topologies.Graph DistributedDatalogToHardwareCompiler HardwareProgram DistributedHardwareProgram ComputableGraph.
Import ListNotations.

Section ForwardingCorrect.

Context {node_id : node_idT}.
Context {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.
Context {node_id_set : map.map node_id unit} {node_id_set_ok : map.ok node_id_set}.
Context {node_id_edge_set : map.map node_id node_id_set} {node_id_edge_set_ok : map.ok node_id_edge_set}.

Abbreviation node_graph := (@ComputableGraph.ComputableGraph node_id node_id_set node_id_edge_set).

Context {forwarding_table : map.map rel_id (list destination)}
        {forwarding_table_ok : map.ok forwarding_table}.
Context {node_ftable_map : map.map node_id forwarding_table}
        {node_ftable_map_ok : map.ok node_ftable_map}.

Abbreviation get_node_ftable node ftables := (get_or_default ftables node).
Abbreviation add_trie_dest := DistributedDatalogToHardwareCompiler.add_trie_dest_to_forwarding_table.
Abbreviation add_path := DistributedDatalogToHardwareCompiler.add_path_to_forwarding_table.

(* the [DestEdge] targets among a destination list *)
Definition dest_edges (ds : list destination) : list node_id :=
  flat_map (fun d => match d with
                     | DistributedHardwareProgram.DestEdge n => [n]
                     | DistributedHardwareProgram.DestTrie _ => [] end) ds.

(* [x] is a [DestEdge] target of [ds] iff [DestEdge x] is literally in [ds]. *)
Lemma In_dest_edges (x : node_id) (ds : list destination) :
  In x (dest_edges ds) <-> In (DistributedHardwareProgram.DestEdge x) ds.
Proof.
  unfold dest_edges. rewrite in_flat_map. split.
  - intros [d [Hin Hx]]. destruct d as [n|t]; cbn in Hx; [|destruct Hx].
    destruct Hx as [<-|[]]. exact Hin.
  - intros Hin. exists (DistributedHardwareProgram.DestEdge x). split; [exact Hin | left; reflexivity].
Qed.

(* the compiler now grows destination lists with coqutil's [list_union eqb]; membership
   distributes over it, so [dest_edges] does too. *)
Lemma dest_edges_union (A B : list destination) (x : node_id) :
  In x (dest_edges (list_union eqb A B)) <-> In x (dest_edges A) \/ In x (dest_edges B).
Proof.
  rewrite !In_dest_edges. apply In_list_union_spec.
Qed.

(* a list of only [DestTrie]s contributes no [DestEdge]s. *)
Lemma dest_edges_map_trie {A : Type} (f : A -> trie_id) (l : list A) :
  dest_edges (List.map (fun t => DistributedHardwareProgram.DestTrie (f t)) l) = [].
Proof. induction l as [|t l IH]; cbn [List.map dest_edges flat_map]; [reflexivity | exact IH]. Qed.

Abbreviation node_id_eqb_spec := (@eqb_boolspec node_id node_id_eqb node_id_eqb_ok).

(* the forwarding edges node [node] has for relation [rel] in [ftables] *)
Definition node_rel_dests (ftables : node_ftable_map) (node : node_id) (rel : rel_id) : list destination :=
  match map.get (get_node_ftable node ftables) rel with Some ds => ds | None => [] end.

Definition has_fwd_edge (ftables : node_ftable_map) (node : node_id) (rel : rel_id) (m : node_id) : Prop :=
  In m (dest_edges (node_rel_dests ftables node rel)).

(*----dest_edges facts----*)

Lemma dest_edges_mono (new ds : list destination) (x : node_id) :
  In x (dest_edges ds) -> In x (dest_edges (list_union eqb new ds)).
Proof. intros H. apply dest_edges_union. right. exact H. Qed.

Lemma dest_edges_add_edge (m : node_id) (ds : list destination) :
  In m (dest_edges (list_union eqb [DistributedHardwareProgram.DestEdge m] ds)).
Proof. apply dest_edges_union. left. apply In_dest_edges. left. reflexivity. Qed.

(* a [list_union] whose fresh list is only [DestTrie]s adds no [DestEdge]. *)
Lemma dest_edges_trie_union_inv {A : Type} (f : A -> trie_id) (l : list A) (ds : list destination) (x : node_id) :
  In x (dest_edges (list_union eqb (List.map (fun t => DistributedHardwareProgram.DestTrie (f t)) l) ds)) ->
  In x (dest_edges ds).
Proof.
  intros H. apply dest_edges_union in H. destruct H as [H|H]; [|exact H].
  rewrite dest_edges_map_trie in H. destruct H.
Qed.

(*----how a map.put changes node_rel_dests----*)

Lemma node_rel_dests_put_diff (ftables : node_ftable_map) (n node : node_id)
    (nf : forwarding_table) (rel : rel_id) :
  n <> node ->
  node_rel_dests (map.put ftables n nf) node rel = node_rel_dests ftables node rel.
Proof.
  intros Hne. unfold node_rel_dests, get_or_default, get_or.
  rewrite map.get_put_diff by (intro; subst; apply Hne; reflexivity). reflexivity.
Qed.

Lemma node_rel_dests_put_same (ftables : node_ftable_map) (node : node_id)
    (nf : forwarding_table) (rel : rel_id) :
  node_rel_dests (map.put ftables node nf) node rel =
  match map.get nf rel with Some ds => ds | None => [] end.
Proof.
  unfold node_rel_dests, get_or_default, get_or. rewrite map.get_put_same. reflexivity.
Qed.

(* the rel-dests at [node0] right after [putting] a fresh value [V] for [rel] there is exactly [V] *)
Lemma node_rel_dests_put_self (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (V : list destination) :
  node_rel_dests (map.put ftables node0 (map.put (get_node_ftable node0 ftables) rel V)) node0 rel = V.
Proof.
  rewrite node_rel_dests_put_same. rewrite map.get_put_same. reflexivity.
Qed.

(* Replacing node [node0]'s table by a [rel]-update that only grows [rel]'s destination list
   ([upd] preserves [dest_edges]) never removes any forwarding edge. *)
Lemma has_fwd_edge_put_relupdate (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (upd : list destination -> list destination) (node : node_id) (rel0 : rel_id) (m : node_id) :
  (forall ds x, In x (dest_edges ds) -> In x (dest_edges (upd ds))) ->
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (map.put ftables node0
                 (map.put (get_node_ftable node0 ftables) rel (upd (node_rel_dests ftables node0 rel))))
               node rel0 m.
Proof.
  intros Hupd Hhas. unfold has_fwd_edge in *.
  destruct (node_id_eqb_spec node node0) as [->|Hne].
  - rewrite node_rel_dests_put_same.
    destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
    + rewrite map.get_put_same. apply Hupd. exact Hhas.
    + rewrite map.get_put_diff by (intro; subst; apply Hrne; reflexivity).
      unfold node_rel_dests in Hhas. exact Hhas.
  - rewrite node_rel_dests_put_diff by congruence. exact Hhas.
Qed.

(* [add_trie_dest] (which only adds [DestTrie]s) never removes a forwarding edge *)
Lemma add_trie_mono (node0 : node_id) (rel : rel_id) (ninfos : list node_info)
    (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id) :
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (add_trie_dest node0 rel ftables ninfos) node rel0 m.
Proof.
  intros Hhas. unfold DistributedDatalogToHardwareCompiler.add_trie_dest_to_forwarding_table.
  apply (has_fwd_edge_put_relupdate ftables node0 rel
           (fun ds => list_union eqb
                        (List.map (fun t => DistributedHardwareProgram.DestTrie t.(tid)) _) ds)).
  - intros ds x Hx. apply dest_edges_mono. exact Hx.
  - exact Hhas.
Qed.

(* the whole [add_path] construction is monotone: it never removes a forwarding edge *)
Lemma add_path_mono (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id),
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (add_path ninfos rel ftables path) node rel0 m.
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables node rel0 m Hhas; cbn.
  - exact Hhas.
  - apply add_trie_mono. exact Hhas.
  - apply IH.
    apply (has_fwd_edge_put_relupdate ftables node0 rel
             (fun ds => list_union eqb [DistributedHardwareProgram.DestEdge next] ds)).
    + intros ds x Hx. apply dest_edges_mono. exact Hx.
    + exact Hhas.
Qed.

(* one-step unfolding of [add_path] on a 2+-element path (avoids [cbn] over-unfolding the fix
   into a stuck [match] on the abstract tail) *)
Lemma add_path_cons2 (rel : rel_id) (node0 next : node_id) (rest : list node_id)
    (ftables : node_ftable_map) (ninfos : list node_info) :
  add_path ninfos rel ftables (node0 :: next :: rest) =
  add_path ninfos rel
    (map.put ftables node0
       (map.put (get_node_ftable node0 ftables) rel
          (list_union eqb [DistributedHardwareProgram.DestEdge next]
             (node_rel_dests ftables node0 rel)))) (next :: rest).
Proof. reflexivity. Qed.

(* MAIN (Phase B): along the laid-out path, each node forwards [rel] to its successor. *)
Lemma add_path_adds (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (i : nat) (a b : node_id),
  nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (add_path ninfos rel ftables path) a rel b.
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables i a b Hi Hib.
  - destruct i; discriminate.
  - destruct i; cbn in Hib; [discriminate | destruct i; discriminate].
  - rewrite add_path_cons2. destruct i as [|i'].
    + (* a = node0, b = next: the edge laid at node0, preserved by the rest *)
      cbn in Hi, Hib. injection Hi as <-. injection Hib as <-.
      apply add_path_mono.
      unfold has_fwd_edge. rewrite node_rel_dests_put_self.
      apply (dest_edges_add_edge next).
    + (* recurse into the tail *)
      apply (IH _ i' a b).
      * cbn in Hi. exact Hi.
      * cbn in Hib. exact Hib.
Qed.

(*============================================================================*)
(*  Phase C (soundness): every forwarding edge is a real graph edge            *)
(*============================================================================*)

Lemma node_rel_dests_put_self_diff (ftables : node_ftable_map) (node0 : node_id) (rel : rel_id)
    (V : list destination) (rel0 : rel_id) :
  rel0 <> rel ->
  node_rel_dests (map.put ftables node0 (map.put (get_node_ftable node0 ftables) rel V)) node0 rel0 =
  node_rel_dests ftables node0 rel0.
Proof.
  intros Hne. rewrite node_rel_dests_put_same.
  rewrite map.get_put_diff by (intro; subst; apply Hne; reflexivity).
  reflexivity.
Qed.

Lemma dest_edges_add_edge_inv (next : node_id) (ds : list destination) (m : node_id) :
  In m (dest_edges (list_union eqb [DistributedHardwareProgram.DestEdge next] ds)) ->
  m = next \/ In m (dest_edges ds).
Proof.
  intros H. apply dest_edges_union in H. destruct H as [H|H].
  - apply In_dest_edges in H. destruct H as [Heq|[]]. injection Heq as ->. left. reflexivity.
  - right. exact H.
Qed.

(* [add_trie_dest] only adds [DestTrie]s, so it changes no forwarding edge *)
Lemma add_trie_edges (node0 : node_id) (rel : rel_id) (ninfos : list node_info)
    (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id) :
  has_fwd_edge (add_trie_dest node0 rel ftables ninfos) node rel0 m ->
  has_fwd_edge ftables node rel0 m.
Proof.
  unfold has_fwd_edge, DistributedDatalogToHardwareCompiler.add_trie_dest_to_forwarding_table. cbv zeta. intros H.
  destruct (node_id_eqb_spec node node0) as [->|Hne].
  - destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
    + rewrite node_rel_dests_put_self in H. apply dest_edges_trie_union_inv in H. exact H.
    + rewrite node_rel_dests_put_self_diff in H by exact Hrne. exact H.
  - rewrite node_rel_dests_put_diff in H by congruence. exact H.
Qed.

(* characterization of [add_path]'s edges: each is either pre-existing or a path step *)
Lemma add_path_edges (rel : rel_id) (ninfos : list node_info) :
  forall (path : list node_id) (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id),
  has_fwd_edge (add_path ninfos rel ftables path) node rel0 m ->
  has_fwd_edge ftables node rel0 m \/
  (rel0 = rel /\ exists i, nth_error path i = Some node /\ nth_error path (S i) = Some m).
Proof.
  induction path as [|node0 [|next rest] IH]; intros ftables node rel0 m H.
  - left. exact H.
  - left. eapply add_trie_edges. exact H.
  - rewrite add_path_cons2 in H.
    destruct (IH _ node rel0 m H) as [H1 | [-> [i [Hi Hib]]]].
    + (* edge in the put: pre-existing, or the (node0 -> next) step *)
      unfold has_fwd_edge in H1.
      destruct (node_id_eqb_spec node node0) as [->|Hne].
      * destruct (Nat.eqb_spec rel0 rel) as [->|Hrne].
        -- rewrite node_rel_dests_put_self in H1.
           apply dest_edges_add_edge_inv in H1. destruct H1 as [-> | H1].
           ++ right. split; [reflexivity|]. exists 0. cbn. split; reflexivity.
           ++ left. exact H1.
        -- left. rewrite node_rel_dests_put_self_diff in H1 by exact Hrne. exact H1.
      * left. rewrite node_rel_dests_put_diff in H1 by congruence. exact H1.
    + (* step inside the tail [next::rest] at index i => index (S i) in the full path *)
      right. split; [reflexivity|]. exists (S i). cbn. split; [exact Hi | exact Hib].
Qed.

(* the table is *edge-sound* when every forwarding edge it records is a real graph edge *)
Definition ftable_edges_sound (g : node_graph) (ftables : node_ftable_map) : Prop :=
  forall node rel m, has_fwd_edge ftables node rel m -> cg_edge g node m.

(* the empty table is edge-sound (it records nothing) *)
Lemma ftable_edges_sound_empty (g : node_graph) : ftable_edges_sound g map.empty.
Proof.
  intros node rel m H. unfold has_fwd_edge, node_rel_dests, get_or_default, get_or in H.
  rewrite map.get_empty in H. simpl in H. cbv [default map_default] in H.
  rewrite map.get_empty in H. simpl in H. destruct H.
Qed.

(* laying down a real edge-path keeps the table edge-sound *)
Lemma add_path_pres_sound (g : node_graph) (rel : rel_id) (ninfos : list node_info)
    (path : list node_id) (ftables : node_ftable_map) (s e : node_id) :
  is_path g s e path ->
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (add_path ninfos rel ftables path).
Proof.
  intros [_ [_ [_ Hwalk]]] Hsound node rel0 m H.
  apply add_path_edges in H. destruct H as [H | [_ [i [Hi Hib]]]].
  - exact (Hsound node rel0 m H).
  - exact (Hwalk i node m Hi Hib).
Qed.

(* the compiler assembles a relation's routing as [add_paths_to_forwarding_table] = a [fold_left]
   of [add_path] over the paths [get_path] found; lift the per-path facts to the whole fold. *)
Lemma add_paths_mono (rel : rel_id) (ninfos : list node_info) (paths : list (list node_id))
    (ftables : node_ftable_map) (node : node_id) (rel0 : rel_id) (m : node_id) :
  has_fwd_edge ftables node rel0 m ->
  has_fwd_edge (DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table rel paths ftables ninfos) node rel0 m.
Proof.
  unfold DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table. revert ftables.
  induction paths as [|path paths IH]; intros ftables Hhas; cbn [fold_left]; [exact Hhas|].
  apply IH. apply add_path_mono. exact Hhas.
Qed.

Lemma add_paths_pres_sound (g : node_graph) (rel : rel_id) (ninfos : list node_info)
    (paths : list (list node_id)) (ftables : node_ftable_map) :
  Forall (fun path => exists s e, is_path g s e path) paths ->
  ftable_edges_sound g ftables ->
  ftable_edges_sound g (DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table rel paths ftables ninfos).
Proof.
  unfold DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table. revert ftables.
  induction paths as [|path paths IH]; intros ftables HF Hsound; cbn [fold_left]; [exact Hsound|].
  inversion HF as [|? ? [s [e Hpath]] HF']; subst.
  apply IH; [exact HF'|].
  exact (add_path_pres_sound g rel ninfos path ftables s e Hpath Hsound).
Qed.

Lemma add_paths_adds (rel : rel_id) (ninfos : list node_info) (paths : list (list node_id))
    (ftables : node_ftable_map) (path : list node_id) (i : nat) (a b : node_id) :
  In path paths -> nth_error path i = Some a -> nth_error path (S i) = Some b ->
  has_fwd_edge (DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table rel paths ftables ninfos) a rel b.
Proof.
  intros Hin Hi Hib.
  unfold DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table. revert ftables Hin.
  induction paths as [|p paths IH]; intros ftables Hin; cbn [fold_left]; [destruct Hin|].
  destruct Hin as [-> | Hin].
  - change (fold_left (add_path ninfos rel) paths (add_path ninfos rel ftables path))
      with (DistributedDatalogToHardwareCompiler.add_paths_to_forwarding_table rel paths (add_path ninfos rel ftables path) ninfos).
    apply add_paths_mono. exact (add_path_adds rel ninfos path ftables i a b Hi Hib).
  - apply IH. exact Hin.
Qed.

(*============================================================================*)
(*  Phase C2 (completeness engine): a forwarding edge laid down by some step    *)
(*  of the construction survives to the final table.  Generic over an arbitrary *)
(*  monotone table-predicate [P] (instantiated with [fun ft => has_fwd_edge     *)
(*  ft a r b] at the use site), threaded through the [fold_left] over rels.     *)
(*============================================================================*)

(* if some element [x0] of [l] has a step that always establishes [P], and every step is
   monotone for [P], then the whole [fold_left] establishes [P]. *)
Lemma fold_left_adds {A : Type} (P : node_ftable_map -> Prop) (f : node_ftable_map -> A -> node_ftable_map)
    (l : list A) (init : node_ftable_map) (x0 : A) :
  In x0 l ->
  (forall acc x, P acc -> P (f acc x)) ->
  (forall acc, P (f acc x0)) ->
  P (fold_left f l init).
Proof.
  intros Hin Hmono Hx0. revert init Hin.
  induction l as [|x l IH]; intros init Hin; cbn; [destruct Hin|].
  destruct Hin as [-> | Hin].
  - apply fold_left_inv; [apply Hx0 | intros acc x _; apply Hmono].
  - apply (IH (f init x) Hin).
Qed.

End ForwardingCorrect.
