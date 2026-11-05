From Stdlib Require Import List Bool ZArith Lia.
From coqutil Require Import Datatypes.List Datatypes.ListSet Map.Interface Map.Properties Datatypes.Result Eqb.
From Datalog Require Import Datalog NattifyRel RelMap.
From Datalog.Util Require Import List Map Default Pftree Eqb.
From DatalogRocq Require Import Topologies.Graph HardwareProgram DistributedHardwareProgram
  DistributedDatalogToHardwareCompiler ComputableGraph MapInstances VariableOrdering.
From DatalogRocq Require Import DistributedHardwareSemantics.
From GraphSearch Require Import GraphInterface Examples.

Import ListNotations.

#[local] Existing Instance rel_id.
#[local] Existing Instance no_fns.
#[local] Existing Instance no_agg.

Section CompileCorrect.
Context {exprvar : exprvarT} {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.
Context {value : valueT} {semantics : datalog_semantics no_fns no_agg value}.
Context {value_eqb : Eqb value} {value_eqb_ok : Eqb_ok value_eqb}.
Context {value_set : map.map (list value) unit} {value_set_ok : map.ok value_set}.
Context {src_ctx : map.map exprvar value} {src_ctx_ok : map.ok src_ctx}.
Context {isa_ctx : map.map var_idx value} {isa_ctx_ok : map.ok isa_ctx}.
Context {node_id : node_idT} {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.
Context {map_node_id_unit : map.map node_id unit} {map_node_id_unit_ok : map.ok map_node_id_unit}.
Context {layout_map : map.map node_id (list rule)} {layout_map_ok : map.ok layout_map}.
Context {fact_locations_map : map.map rel_id (list node_id)} {fact_locations_map_ok : map.ok fact_locations_map}.
Context {fwd_tbl : map.map (rel_id * fwd_from) (list fwd_to)} {fwd_tbl_ok : map.ok fwd_tbl}.
Context {graph_vnode : graph.graph vnode} {graph_vnode_ok : graph.ok graph_vnode}.
Context {graph_node_id : graph.graph node_id}.
Context {network_map : map.map node_id node_info} {network_map_ok : map.ok network_map}.
Context {node_ftable_map : map.map node_id forwarding_table} {node_ftable_map_ok : map.ok node_ftable_map}.
Context {rels_at_node : map.map node_id (list rel_id)} {rels_at_node_ok : map.ok rels_at_node}.

Definition good_source_rule (r : rule) :=
  match r with
  | rule.impl concls hyps =>
      Forall (fun c => NoDup (clause.vars c)) hyps /\
        incl (flat_map clause.vars concls) (flat_map clause.vars hyps)
  | rule.agg _ a _ => match a with end
  end.

Definition good_source_ruleb (r : rule) :=
  match r with
  | rule.impl concls hyps =>
      andb (forallb (fun c => nodupb (clause.vars c)) hyps)
        (inclb (flat_map clause.vars concls) (flat_map clause.vars hyps))
  | rule.agg _ a _ => match a with end
  end.

Lemma good_source_ruleb_spec r : good_source_ruleb r = true -> good_source_rule r.
Proof.
  destruct r as [concls hyps|]; [|contradiction]. cbn. intros H.
  apply andb_prop in H as [H1 H2]. rewrite forallb_forall in H1. split.
  - apply Forall_forall. intros c Hc. apply nodupb_sound, H1, Hc.
  - apply inclb_incl, H2.
Qed.

Lemma good_source_rulesb_spec rs : forallb good_source_ruleb rs = true -> Forall good_source_rule rs.
Proof. rewrite forallb_forall. intros H. apply Forall_forall. intros r Hr. apply good_source_ruleb_spec, H, Hr. Qed.

Lemma map_var_of_expr_varmap (f : exprvar -> var_idx) (args : list expr) :
  map var_of_expr (map (expr_varmap f) args) = map f (flat_map expr.vars args).
Proof. induction args as [|[|[]] args IH]; [reflexivity|]. cbn. f_equal. exact IH. Qed.

Lemma lookup_injective (order : list exprvar) x y :
  In x order -> In y order ->
  unwrap_or_default (index_of x order) = unwrap_or_default (index_of y order) -> x = y.
Proof.
  intros Hx Hy H.
  destruct (index_of_In _ _ Hx) as (i & Hi & Hni). destruct (index_of_In _ _ Hy) as (j & Hj & Hnj).
  rewrite Hi, Hj in H. cbn in H. subst j. congruence.
Qed.

Lemma order_variables_good r :
  good_source_rule r -> good_rule (order_variables r).
Proof.
  destruct r as [concls hyps|]; [|contradiction]. intros [Hnd _]. cbv [good_rule order_variables].
  pose proof (variable_order_ok hyps) as [_ Hset].
  apply Forall_forall. intros c' Hc'. apply in_map_iff in Hc'. destruct Hc' as [c [<- Hc]].
  rewrite Forall_forall in Hnd. cbv [clause_varmap]. cbn [clause.args].
  rewrite map_var_of_expr_varmap. apply Finite.Injective_map_NoDup_in; [|exact (Hnd c Hc)].
  intros x y Hx Hy. apply lookup_injective; apply Hset, in_flat_map; eauto.
Qed.

Lemma order_variables_interp r nf hyps :
  good_source_rule r -> rule.interp (order_variables r) nf hyps <-> rule.interp r nf hyps.
Proof.
  destruct r as [concls hs|]; [|contradiction]. intros [_ Hincl]. cbv [order_variables].
  apply rule_interp_impl_varmap.
  pose proof (variable_order_ok hs) as [_ Hset].
  intros x y Hx Hy. rewrite flat_map_app, in_app_iff in Hx, Hy.
  apply lookup_injective; apply Hset; [destruct Hx as [Hx|Hx] | destruct Hy as [Hy|Hy]];
    auto using Hincl.
Qed.

Definition node_fires (ni : node_info) (nf : normal_fact) (hyps : list fact) :=
  exists tr r, In tr ni.(node_info.program) /\
            trie_rule.interp (nth_error ni.(node_info.tries)) tr r /\ rule.interp r nf hyps.

Lemma compile_node_fires rs ft nf hyps :
  Forall good_source_rule rs ->
  node_fires (compile_node rs ft) nf hyps <-> Exists (fun r => rule.interp r nf hyps) rs.
Proof.
  intros Hrs. cbv [node_fires compile_node]. cbn [node_info.program node_info.tries].
  set (rs' := map order_variables rs).
  assert (Hgood : Forall good_rule rs').
  { apply Lists.List.Forall_map. eapply Forall_impl; [exact Hrs | exact order_variables_good]. }
  rewrite Forall_forall in Hrs. rewrite Exists_exists. unfold trie_rule.of_rules. split.
  - intros (tr & r & Htr & Hr & Hfire).
    apply in_map_iff in Htr. destruct Htr as [r' [<- Hr']].
    rewrite (trie_rule.interp_functional _ _ _ _ Hr (trie_rule.interp_of_rule_in rs' r' Hgood Hr')) in Hfire.
    apply in_map_iff in Hr'. destruct Hr' as [r0 [<- Hr0]].
    exists r0. split; [exact Hr0|]. apply (order_variables_interp r0); auto.
  - intros [r0 [Hr0 Hfire]].
    exists (trie_rule.of_rule (trie.of_rules rs') (order_variables r0)), (order_variables r0).
    split; [|split].
    + apply in_map, in_map, Hr0.
    + apply trie_rule.interp_of_rule_in; [exact Hgood | apply in_map, Hr0].
    + apply order_variables_interp; auto.
Qed.

Lemma get_compile_all_nodes (layout : layout_map) (ftables : node_ftable_map) n :
  get_or_default (compile_all_nodes layout ftables) n =
    compile_node (get_or_default layout n) (get_or_default ftables n).
Proof.
  unfold compile_all_nodes.
  set (keys := list_union eqb (map.keys layout) (map.keys ftables)).
  assert (Hfst : map fst (map (fun n => (n, compile_node (get_or_default layout n) (get_or_default ftables n))) keys) = keys).
  { rewrite map_map. apply map_id. }
  destruct (inb_spec n keys) as [Hin|Hnin].
  - rewrite <- Hfst in Hin. destruct (in_of_list_Some_strong _ _ Hin) as [v [Hget Hv]].
    rewrite (get_or_default_Some _ _ _ Hget). apply in_map_iff in Hv.
    destruct Hv as [n' [Heq _]]. injection Heq as -> <-. reflexivity.
  - rewrite get_or_default_None by (apply get_of_list_not_In; rewrite Hfst; exact Hnin).
    assert (Hl : map.get layout n = None).
    { destruct (map.get layout n) eqn:E; [|reflexivity].
      exfalso. apply Hnin, In_list_union_spec. left. eapply map.in_keys. exact E. }
    assert (Hf : map.get ftables n = None).
    { destruct (map.get ftables n) eqn:E; [|reflexivity].
      exfalso. apply Hnin, In_list_union_spec. right. eapply map.in_keys. exact E. }
    rewrite (get_or_default_None _ _ Hl), (get_or_default_None _ _ Hf). reflexivity.
Qed.

Lemma source_program_in (layout : layout_map) (r : rule) :
  In r (source_program layout) <-> exists n p, map.get layout n = Some p /\ In r p.
Proof. unfold source_program. apply In_concat_values. Qed.

Lemma rule_in_source_program (layout : layout_map) (n : node_id) (r : rule) :
  In r (get_or_default layout n) -> In r (source_program layout).
Proof.
  intros Hr. destruct (map.get layout n) as [p|] eqn:Hget.
  - apply source_program_in. exists n, p. rewrite (get_or_default_Some _ _ _ Hget) in Hr. auto.
  - rewrite (get_or_default_None _ _ Hget) in Hr. destruct Hr.
Qed.

Lemma get_map_values (fr : list rule -> list rel_id) (m : layout_map) (n : node_id) :
  map.get (@map.map_values node_id (list rule) (list rel_id) layout_map rels_at_node fr m) n
  = option_map fr (map.get m n).
Proof.
  unfold map.map_values. revert n. eapply map.fold_spec.
  - intros n. rewrite !map.get_empty. reflexivity.
  - intros k0 v m0 acc Hget IH n. rewrite map.get_put_dec, IH, map.get_put_dec.
    destruct (eqb k0 n); reflexivity.
Qed.

Lemma in_internal_iff (fr : rule -> list rel_id) (layout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (invert (map.map_values (fun p => dedup (flat_map fr p)) layout)) R)
  <-> exists r, In r (get_or_default layout n) /\ In R (fr r).
Proof.
  rewrite in_get_or_default_invert, get_map_values.
  destruct (map.get layout n) as [p|] eqn:Hn; cbn [option_map].
  - rewrite (get_or_default_Some _ _ _ Hn). split.
    + intros [bs [Heq Hin]]. injection Heq as <-. rewrite dedup_In in Hin. apply in_flat_map in Hin. exact Hin.
    + intros [r [Hr HRr]]. exists (dedup (flat_map fr p)). split; [reflexivity|].
      rewrite dedup_In. apply in_flat_map. exists r. split; assumption.
  - rewrite (get_or_default_None _ _ Hn). split.
    + intros [bs [Heq _]]. discriminate.
    + intros [r [[] _]].
Qed.

Definition edb_routable (lfp : fact_locations_map) (Q : fact -> Prop) : Prop :=
  forall f, Q f -> exists n, In n (get_or_default lfp (fact.rel f)).

Lemma node_consumes_internal (layout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (get_internal_consumers_of layout) R)
  <-> exists r, In r (get_or_default layout n) /\ In R (rule.hyp_rels r).
Proof. unfold get_internal_consumers_of. apply in_internal_iff. Qed.

Lemma node_produces_internal (layout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (get_internal_producers_of layout) R)
  <-> exists r, In r (get_or_default layout n) /\ In R (rule.concl_rels r).
Proof. unfold get_internal_producers_of. apply in_internal_iff. Qed.

Lemma In_get_or_default {K V} {M : map.map K (list V)} (m : M) (k : K) (x : V) :
  In x (get_or_default m k) -> exists l, map.get m k = Some l /\ In x l.
Proof. unfold get_or_default, get_or. destruct (map.get m k) as [l|]; [eauto | intros []]. Qed.

Lemma In_keys_of_In_get_or_default {K V} {keqb : Eqb K} {keqb_ok : Eqb_ok keqb}
    {M : map.map K (list V)} {M_ok : map.ok M} (m : M) (k : K) (x : V) :
  In x (get_or_default m k) -> In k (map.keys m).
Proof. intros Hx. destruct (In_get_or_default m k x Hx) as [l [Hget _]]. exact (map.in_keys _ _ _ Hget). Qed.

Lemma In_get_or_default_union_with {K V} {keqb : Eqb K} {keqb_ok : Eqb_ok keqb}
    {veqb : Eqb V} {veqb_ok : Eqb_ok veqb} {M : map.map K (list V)} {M_ok : map.ok M}
    (m1 m2 : M) (k : K) (x : V) :
  In x (get_or_default m1 k) \/ In x (get_or_default m2 k) ->
  In x (get_or_default (union_with (list_union eqb) m1 m2) k).
Proof.
  intros [Hx | Hx]; destruct (In_get_or_default _ k x Hx) as [l [Hget Hxl]];
    unfold get_or_default, get_or; rewrite union_with_get, Hget.
  - destruct (map.get m2 k); [apply In_list_union_spec; left|]; exact Hxl.
  - destruct (map.get m1 k); [apply In_list_union_spec; right|]; exact Hxl.
Qed.

Lemma get_of_list_const {K V} {keqb : Eqb K} {keqb_ok : Eqb_ok keqb}
    {M : map.map K V} {M_ok : map.ok M} (ks : list K) (v : V) (k : K) :
  In k ks -> map.get (map.of_list (List.map (fun k => (k, v)) ks) : M) k = Some v.
Proof.
  induction ks as [|k0 ks IH]; cbn; [intros []|]. intros Hk.
  rewrite map.get_put_dec. destruct (eqb_boolspec _ k0 k) as [<-|Hne]; [reflexivity|].
  destruct Hk as [->|Hk]; [congruence | auto].
Qed.

Lemma producer_internal (layout : layout_map) (ins_rels : list rel_id) (R : rel_id) (n : node_id) (r : rule) :
  In r (get_or_default layout n) -> In R (rule.concl_rels r) ->
  In (vnode.at_port n fwd_from.self) (get_or_default (get_all_producers_of layout ins_rels) R).
Proof.
  intros Hr HR. unfold get_all_producers_of. cbv zeta.
  apply In_get_or_default_union_with. left.
  destruct (In_get_or_default _ R n (proj2 (node_produces_internal layout n R) (ex_intro _ r (conj Hr HR))))
    as [ns [Hget Hns]].
  destruct (map.map_values_fw (fun nodes => List.map (fun n => vnode.at_port n fwd_from.self) nodes)
              _ _ eq_refl _ _ Hget) as [vs [<- Hvs]].
  erewrite get_or_default_Some; [|exact Hvs]. apply in_map_iff. eauto.
Qed.

Lemma producer_input (layout : layout_map) (ins_rels : list rel_id) (R : rel_id) :
  In R ins_rels -> In vnode.ext_input (get_or_default (get_all_producers_of layout ins_rels) R).
Proof.
  intros HR. unfold get_all_producers_of. cbv zeta.
  apply In_get_or_default_union_with. right.
  erewrite get_or_default_Some; [|apply get_of_list_const; exact HR]. left. reflexivity.
Qed.

Lemma consumer_internal (layout : layout_map) (outs_rels : list rel_id) (R : rel_id) (n : node_id) (r : rule) :
  In r (get_or_default layout n) -> In R (rule.hyp_rels r) ->
  In (vnode.fact_dst n) (get_or_default (get_all_consumers_of layout outs_rels) R).
Proof.
  intros Hr HR. unfold get_all_consumers_of. cbv zeta.
  apply In_get_or_default_union_with. left.
  destruct (In_get_or_default _ R n (proj2 (node_consumes_internal layout n R) (ex_intro _ r (conj Hr HR))))
    as [ns [Hget Hns]].
  destruct (map.map_values_fw (fun nodes => List.map vnode.fact_dst nodes) _ _ eq_refl _ _ Hget)
    as [vs [<- Hvs]].
  erewrite get_or_default_Some; [|exact Hvs]. apply in_map_iff. eauto.
Qed.

Lemma consumer_output (layout : layout_map) (outs_rels : list rel_id) (R : rel_id) :
  In R outs_rels -> In vnode.ext_output (get_or_default (get_all_consumers_of layout outs_rels) R).
Proof.
  intros HR. unfold get_all_consumers_of. cbv zeta.
  apply In_get_or_default_union_with. right.
  erewrite get_or_default_Some; [|apply get_of_list_const; exact HR]. left. reflexivity.
Qed.

Lemma reaches_closed {V} {G : graph.graph V} (g : graph V) (P : V -> Prop) (u v : V) :
  (forall x y, P x -> graph.edge g x y -> P y) -> P u -> graph.reaches g u v -> P v.
Proof.
  intros Hstep Hu [p [Hp Hv]]. subst v. revert u Hu Hp.
  induction p as [|x p IH]; intros u Hu Hp; [exact Hu|].
  destruct Hp as [He Hp]. rewrite GraphSearch.List.last_cons. eauto.
Qed.

Lemma fed_reaches (g : rel_id -> graph vnode) (producers consumers : partial_map rel_id (list vnode))
    (R : rel_id) (p c : vnode) :
  all_consumers_fed g producers consumers = true ->
  In p (get_or_default producers R) -> In c (get_or_default consumers R) ->
  graph.reaches (g R) p c.
Proof.
  intros Hfed Hp Hc. destruct (In_get_or_default _ R c Hc) as [cs [Hget Hcs]].
  unfold all_consumers_fed in Hfed.
  eapply map.get_forallb in Hfed; [|exact Hget].
  unfold all_consumers_fed_for_relation in Hfed.
  rewrite forallb_forall in Hfed. specialize (Hfed p Hp). cbv beta in Hfed.
  apply inclb_incl in Hfed. apply graph.get_reachable_nodes_spec, Hfed, Hcs.
Qed.

Lemma check_ftables_routable_fed (ftables : node_ftable_map) (ins : fact_locations_map)
    (producers consumers : partial_map rel_id (list vnode)) :
  check_ftables_routable ftables ins producers consumers = Success tt ->
  all_consumers_fed (fun R => graph.of_edges (graph_of_ftables_at (get_or_default ins R) ftables R))
    producers consumers = true.
Proof.
  unfold check_ftables_routable. cbv zeta.
  destruct (all_consumers_fed _ _ _); [reflexivity | discriminate].
Qed.

Section Routing.
Context (ninfos : node_id -> node_info) (ft : node_ftable_map)
        (Hfwd : forall n R src, forward (ninfos n) R src = get_or_default (get_or_default ft n) (R, src))
        (ins : fact_locations_map) (Q : fact -> Prop).

Local Abbreviation input := (fun n (f : fact) => Q f /\ In n (get_or_default ins (fact.rel f))).
Local Abbreviation reach := (dreach ninfos input).
Local Abbreviation vgraph R := (graph.of_edges (graph_of_ftables_at (get_or_default ins R) ft R)).

Definition holds_at (f : fact) (v : vnode) : Prop :=
  match v with
  | vnode.at_port n src => exists c, reach c /\ c n src f
  | vnode.fact_dst n => present ninfos input n f
  | vnode.ext_input => Q f
  | vnode.ext_output => run_ninfos ninfos input f
  end.

Lemma vgraph_edge (R : rel_id) (u v : vnode) :
  graph.edge (vgraph R) u v ->
  (exists n src dst, u = vnode.at_port n src /\ v = vnode.target_of n dst /\
     In dst (get_or_default (get_or_default ft n) (R, src)))
  \/ (u = vnode.ext_input /\ exists i, In i (get_or_default ins R) /\ v = vnode.at_port i fwd_from.input).
Proof.
  rewrite graph.edge_of_edges. unfold graph_of_ftables_at.
  rewrite in_app_iff. intros [H | H].
  - left. apply in_flat_map in H. destruct H as [[n ftn] [Htup H]]. apply map.tuples_spec in Htup.
    unfold graph_of_ftable_at in H.
    apply in_flat_map in H. destruct H as [[[R' src] dsts] [Htup' H]]. apply map.tuples_spec in Htup'.
    revert H. destruct (eqb_boolspec _ R R') as [<-|_]; intros H; [|destruct H].
    apply in_map_iff in H. destruct H as [dst [Heq Hdst]]. injection Heq as <- <-.
    exists n, src, dst. split; [reflexivity|]. split; [reflexivity|].
    rewrite (get_or_default_Some _ _ _ Htup), (get_or_default_Some _ _ _ Htup'). exact Hdst.
  - right. apply in_map_iff in H. destruct H as [i [Heq Hi]]. injection Heq as <- <-. eauto.
Qed.

Lemma holds_at_edge (u v : vnode) (f : fact) :
  graph.edge (vgraph (fact.rel f)) u v -> holds_at f u -> holds_at f v.
Proof.
  intros He Hu.
  destruct (vgraph_edge _ _ _ He) as [(n & src & dst & -> & -> & Hdst) | (-> & i & Hi & ->)].
  - destruct Hu as [c [Hrc Hc]]. rewrite <- Hfwd in Hdst.
    destruct dst as [| | n' ch]; cbn.
    + exists n, src, c. auto.
    + exists c, src. auto.
    + exists (cadd c n' (fwd_from.node n ch) f). split.
      * eapply dreachS; [exact Hrc | eapply dstep_forward; eassumption].
      * unfold cadd. right. auto.
  - exists (cadd (fun _ _ _ => False) i fwd_from.input f). split.
    + eapply dreachS; [apply dreach0 | apply dstep_input; split; assumption].
    + unfold cadd. right. auto.
Qed.

Lemma holds_at_reaches (u v : vnode) (f : fact) :
  graph.reaches (vgraph (fact.rel f)) u v -> holds_at f u -> holds_at f v.
Proof. intros Hr Hu. eapply reaches_closed; [| exact Hu | exact Hr]. intros. eapply holds_at_edge; eauto. Qed.

Context (layout : layout_map) (outs : fact_locations_map).
Context (Hmatch : forall n nf hyps,
            node_fires (ninfos n) nf hyps <-> Exists (fun r => rule.interp r nf hyps) (get_or_default layout n)).

Local Abbreviation P := {| program.rules := source_program layout; program.meta_rules := [] |}.

Lemma reach_sound (c : config) :
  reach c -> forall n src f, c n src f -> program.interp P Q f.
Proof.
  induction 1 as [|c c' Hr IH Hstep]; intros n0 src0 f0 Hc; [destruct Hc|].
  inversion Hstep as [n f Hin | n tr r nf hyps Htr Hr' Hfire Hhyps | n n' f src ch Hcnf Hfwd']; subst c';
    unfold cadd in Hc; (destruct Hc as [Hold | (-> & -> & ->)]; [exact (IH _ _ _ Hold)|]).
  - apply pftree.leaf. apply Hin.
  - pose proof (proj1 (Hmatch n nf hyps) (ex_intro _ tr (ex_intro _ r (conj Htr (conj Hr' Hfire))))) as Hex.
    apply Exists_exists in Hex. destruct Hex as [r0 [Hin Hr0]].
    eapply pftree.step with (l := hyps).
    + constructor. apply Exists_exists. exists r0. split; [exact (rule_in_source_program _ _ _ Hin) | exact Hr0].
    + eapply Forall_impl; [exact Hhyps|]. intros h [s [Hs _]]. exact (IH _ _ _ Hs).
  - exact (IH _ _ _ Hcnf).
Qed.

Lemma run_output_sound (f : fact) :
  run_ninfos ninfos input f -> program.interp P Q f.
Proof. intros (n & src & c & Hr & Hc & _). exact (reach_sound c Hr n src f Hc). Qed.

Context (Hfed : all_consumers_fed (fun R => vgraph R)
                  (get_all_producers_of layout (map.keys ins))
                  (get_all_consumers_of layout (map.keys outs)) = true).
Context (HQ : edb_routable ins Q).

Lemma derivable_at_producer (f : fact) :
  program.interp P Q f ->
  exists p, In p (get_or_default (get_all_producers_of layout (map.keys ins)) (fact.rel f)) /\ holds_at f p.
Proof.
  revert f.
  apply (pftree.ind (program.interp_step P) Q
           (fun f => exists p, In p (get_or_default (get_all_producers_of layout (map.keys ins)) (fact.rel f))
                               /\ holds_at f p)).
  - intros f HQf. exists vnode.ext_input. split; [|exact HQf].
    apply producer_input. destruct (HQ f HQf) as [i Hi]. exact (In_keys_of_In_get_or_default _ _ _ Hi).
  - intros f l Hstep _ IH.
    destruct Hstep as [nf l Hex | mf mhyps Hex];
      [|apply Exists_exists in Hex; destruct Hex as [? [[] _]]].
    apply Exists_exists in Hex. destruct Hex as [r [Hrin Hr]].
    apply source_program_in in Hrin. destruct Hrin as [n [pn [Hget Hrpn]]].
    assert (Hrn : In r (get_or_default layout n)) by (rewrite (get_or_default_Some _ _ _ Hget); exact Hrpn).
    assert (Hpres : Forall (fun h => present ninfos input n h) l).
    { apply Forall_forall. intros h Hh. rewrite Forall_forall in IH.
      destruct (IH h Hh) as [p [Hp Hhp]].
      apply (holds_at_reaches p (vnode.fact_dst n) h); [|exact Hhp].
      apply (fed_reaches _ _ _ (fact.rel h) p (vnode.fact_dst n) Hfed Hp).
      apply (consumer_internal layout _ _ n r Hrn).
      apply rule.interp_hyp_relname_in in Hr. rewrite Forall_forall in Hr. exact (Hr h Hh). }
    destruct (present_list ninfos input n l Hpres) as [c [Hrc Hcl]].
    destruct (proj2 (Hmatch n nf l) (proj2 (Exists_exists _ _) (ex_intro _ r (conj Hrn Hr))))
      as (tr & r' & Htr & Hr' & Hfire).
    exists (vnode.at_port n fwd_from.self). split.
    + exact (producer_internal layout _ _ n r Hrn (rule.interp_concl_relname_in _ _ _ Hr)).
    + exists (cadd c n fwd_from.self (fact.normal nf)). split.
      * eapply dreachS; [exact Hrc|]. eapply dstep_run; eassumption.
      * unfold cadd. right. auto.
Qed.

Lemma derivable_output (f : fact) :
  program.interp P Q f -> (exists n, In n (get_or_default outs (fact.rel f))) ->
  run_ninfos ninfos input f.
Proof.
  intros Hf [n Hn]. destruct (derivable_at_producer f Hf) as [p [Hp Hfp]].
  apply (holds_at_reaches p vnode.ext_output f); [|exact Hfp].
  apply (fed_reaches _ _ _ (fact.rel f) p vnode.ext_output Hfed Hp).
  apply consumer_output. exact (In_keys_of_In_get_or_default _ _ _ Hn).
Qed.

End Routing.

Lemma compile_success_extract (layout : layout_map) (outs ins : fact_locations_map)
    (ftables : node_ftable_map) (g : ComputableGraph node_id) (network : network_map) :
  compile layout outs ins ftables g = Success network ->
  network = compile_all_nodes layout ftables /\
    check_ftables_routable ftables ins (get_all_producers_of layout (map.keys ins))
      (get_all_consumers_of layout (map.keys outs)) = Success tt.
Proof.
  intros H. unfold compile in H. cbv zeta in H.
  destruct (check_graph_valid g); cbn beta iota in H; [|discriminate].
  destruct (layout_in_graphb g layout); cbn beta iota in H; [|discriminate].
  destruct (ftables_in_graphb outs g ftables); cbn beta iota in H; [|discriminate].
  destruct (check_ftables_routable ftables ins (get_all_producers_of layout (map.keys ins))
              (get_all_consumers_of layout (map.keys outs))) as [[]|] eqn:Hroute;
    cbn beta iota in H; [|discriminate].
  destruct (check_ftables_acyclic ftables) as [[]|]; cbn beta iota in H; [|discriminate].
  injection H as <-. auto.
Qed.

Theorem compile_distributed_correct
    (layout : layout_map) (outs ins : fact_locations_map) (ftables : node_ftable_map)
    (g : ComputableGraph node_id) (network : network_map) (Q : fact -> Prop) :
  compile layout outs ins ftables g = Success network ->
  Forall good_source_rule (source_program layout) ->
  edb_routable ins Q ->
  forall f, (exists n, In n (get_or_default outs (fact.rel f))) ->
    run_ninfos (get_or_default network) (fun n f0 => Q f0 /\ In n (get_or_default ins (fact.rel f0))) f
    <-> program.interp {| program.rules := source_program layout; program.meta_rules := [] |} Q f.
Proof.
  intros Hcomp Hgood HQ f Hout.
  destruct (compile_success_extract _ _ _ _ _ _ Hcomp) as [-> Hroute].
  assert (Hfwd : forall n R src, forward (get_or_default (compile_all_nodes layout ftables) n) R src =
                            get_or_default (get_or_default ftables n) (R, src)).
  { intros n R src. rewrite get_compile_all_nodes. reflexivity. }
  assert (Hmatch : forall n nf hyps,
             node_fires (get_or_default (compile_all_nodes layout ftables) n) nf hyps <->
               Exists (fun r => rule.interp r nf hyps) (get_or_default layout n)).
  { intros n nf hyps. rewrite get_compile_all_nodes. apply compile_node_fires.
    rewrite Forall_forall in *. eauto using rule_in_source_program. }
  pose proof (check_ftables_routable_fed _ _ _ _ Hroute) as Hfed.
  split.
  - eapply run_output_sound; eassumption.
  - intros Hf. eapply derivable_output; eassumption.
Qed.

Context {rel : relT} {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.

Definition program_rels (p : list (@Datalog.rule rel exprvar no_fns no_agg)) : list rel :=
  flat_map rule.all_rels p.

Local Abbreviation rules_only p := {| program.rules := p; program.meta_rules := [] |}.

Definition relabel_Q (rho : rel -> rel_id) (Q : Datalog.fact (_rel := rel) -> Prop)
    : Datalog.fact (_rel := rel_id) -> Prop :=
  fun f' => exists f, f' = fact.map_rel rho f /\ Q f.

Theorem nattify_and_compile_correct
    (p : list (@Datalog.rule rel exprvar no_fns no_agg))
    (layout : layout_map) (outs ins : fact_locations_map) (ftables : node_ftable_map)
    (g : ComputableGraph node_id) (network : network_map)
    (Qsrc : Datalog.fact (_rel := rel) -> Prop) (fsrc : Datalog.fact (_rel := rel)) :
  compile layout outs ins ftables g = Success network ->
  Forall good_source_rule (source_program layout) ->
  layout_distributes_program
    (NattifyRel.nattify_rel_prog (program_rels p) (rules_only p)).(program.rules) layout ->
  (forall f, Qsrc f -> In (fact.rel f) (program_rels p)) ->
  edb_routable ins (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc) ->
  (exists n, In n (get_or_default outs (fact.rel (nattify_rel_fact (program_rels p) (rules_only p) fsrc)))) ->
  ( run_ninfos (get_or_default network)
      (fun n f0 => relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc f0
                   /\ In n (get_or_default ins (fact.rel f0)))
      (nattify_rel_fact (program_rels p) (rules_only p) fsrc)
    <-> program.interp (rules_only p) Qsrc fsrc ).
Proof.
  intros Hcomp Hgood Hdist Hscope Hedb Houtrel.
  assert (Hset : same_set (source_program layout)
                   (NattifyRel.nattify_rel_prog (program_rels p) (rules_only p)).(program.rules)).
  { destruct Hdist as [Hsub1 Hsub2]. intros r. split; [apply Hsub1 | apply Hsub2]. }
  assert (HB : program.interp (rules_only (source_program layout))
                 (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc)
                 (nattify_rel_fact (program_rels p) (rules_only p) fsrc)
               <-> program.interp (NattifyRel.nattify_rel_prog (program_rels p) (rules_only p))
                 (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc)
                 (nattify_rel_fact (program_rels p) (rules_only p) fsrc)).
  { split; intro H'.
    - eapply program.interp_same_set; [| | exact H']; [exact Hset | intros x; reflexivity].
    - eapply program.interp_same_set; [| | exact H'];
        [exact (fun r => iff_sym (Hset r)) | intros x; reflexivity]. }
  eapply iff_trans;
    [ exact (compile_distributed_correct layout outs ins ftables g network
               (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc)
               Hcomp Hgood Hedb
               (nattify_rel_fact (program_rels p) (rules_only p) fsrc) Houtrel)
    | ].
  eapply iff_trans; [ exact HB | ].
  symmetry.
  apply (nattify_rel_correct (program_rels p) (rules_only p) Qsrc fsrc Hscope).
Qed.

End CompileCorrect.
