(* Correctness of [DistributedDatalogToHardwareCompiler.compile] against the trie-join semantics of [NodeHardwareSemantics],
   for the *bare-variable* (SuperNice) fragment: every hypothesis/conclusion argument is a
   bare variable [expr.var].  (Function-application arguments in premises/conclusions are not yet
   handled by the compiler -- see DistributedDatalogToHardwareCompiler.generate_join / compile_concl -- and are out of
   scope here.)

   The chain is:

     source datalog  --(rename, DistributedDatalogToHardwareCompiler)-->  lowered_program
        |  program.interp                             |  NodeHardwareSemantics.lprog_impl_fact (= Datalog on ids)
        |                                             |  ===  NodeHardwareSemantics.hw_prog_impl_fact
        +---------------------------------------------+      (this file: per-rule bridge)

   [NodeHardwareSemantics.hw_prog_correct] already reduces whole-node correctness to the per-rule predicate
   [hw_rule_matches].  This file works toward [hw_rule_matches] for rules the (now fixed)
   [compile_rule] produces, i.e. the *generic-join correctness*: the trie-join query
   [generate_query] admits exactly the variable bindings under which the lowered rule fires. *)

From Stdlib Require Import List Bool ZArith Lia Relation_Operators.
From coqutil Require Import Datatypes.List Datatypes.ListSet Map.Interface Map.Properties Datatypes.Result Eqb.
From Datalog Require Import Datalog NattifyRel RelMap.
From Datalog.Util Require Import List Map Default Pftree Eqb.
From DatalogRocq Require Import Topologies.Graph HardwareProgram DistributedDatalogToHardwareCompiler NodeHardwareSemantics ComputableGraph MapInstances.
From DatalogRocq Require Import DistributedHardwareSemantics.
From GraphSearch Require Import GraphInterface Examples.

Import ListNotations.

Local Abbreviation nfact R args := (fact.normal {| normal_fact.rel := R; normal_fact.args := args |}).

Section DistributedDatalogToHardwareCompilerCorrect.

Context `{params : datalog_params (_rel := rel_id) (rel_eqb := nat_eqb) (rel_eqb_ok := nat_eqb_ok)}.
Context {var_idx_map : map.map exprvar nat}.   (* used by compute_permutation *)
Context {var_idx_map_ok : map.ok var_idx_map}.

(* the tuple of a (normal) ground fact; meta facts (never produced by the bare fragment)
   read as []. *)
Definition nfargs (f : Datalog.fact (_rel := rel_id)) : list value :=
  match f with nfact _ a => a | _ => [] end.

(*----Trie-generation facts (toward hooking up compile_rule)----*)

(*----Reading the compiler's lowered AST as a Datalog program----*)

(* A [lowered_rule] IS a [Datalog] rule over numeric relation ids ([rel_id]) at the source's
   [exprvar]/[fn]/[aggregator] -- exactly the rule the trie-join semantics verifies.  So there is NO
   [lowered -> Datalog] conversion: the compiler emits these rules in their final type, and
   ([DistributedDatalogToHardwareCompiler.global_rename_rule]/[compile_rule]) error out on any non-[rule.impl], so a
   lowered program is normal by construction.  A lowered fact/expr likewise IS a [Datalog]
   clause/expr over numeric ids. *)

(* [clause.interp] lifted to facts: a lowered clause interprets to the normal fact over its
   relation and its interpreted arguments. *)
Definition interp_fact (ctx : context) (c : lowered_fact) (f : Datalog.fact (_rel := rel_id)) : Prop :=
  exists nf_args,
    Forall2 (expr.interp ctx) c.(Datalog.clause.args) nf_args /\
      f = nfact c.(Datalog.clause.rel) nf_args.

Lemma interp_fact_normal (ctx : context) (c : lowered_fact) (nf : normal_fact) :
  interp_fact ctx c (fact.normal nf) <-> clause.interp ctx c nf.
Proof.
  destruct nf as [R args]. cbv [interp_fact clause.interp]. simpl. split.
  - intros [args' [HF Heq]]. injection Heq as -> ->. auto.
  - intros [-> HF]. eauto.
Qed.

Lemma Forall2_interp_fact (ctx : context) (hyps : list lowered_fact)
    (hyps' : list (Datalog.fact (_rel := rel_id))) :
  Forall2 (interp_fact ctx) hyps hyps' <->
  exists nhyps, hyps' = map fact.normal nhyps /\ Forall2 (clause.interp ctx) hyps nhyps.
Proof.
  split.
  - induction 1 as [|c f hyps hyps' [args [HF ->]] _ [nhyps [-> IH]]].
    + exists []. auto.
    + exists ({| normal_fact.rel := c.(Datalog.clause.rel); normal_fact.args := args |} :: nhyps).
      split; [reflexivity|]. constructor; [|exact IH]. split; [reflexivity | exact HF].
  - intros [nhyps [-> HF]]. induction HF; simpl; constructor; auto.
    apply interp_fact_normal. assumption.
Qed.

Lemma interp_fact_agree_on (ctx1 ctx2 : context) (c : lowered_fact) (f : Datalog.fact (_rel := rel_id)) :
  interp_fact ctx1 c f ->
  Forall (agree_on ctx1 ctx2) (clause.vars c) ->
  interp_fact ctx2 c f.
Proof.
  intros [args [HF ->]] Hag. apply interp_fact_normal.
  eapply clause.interp_agree_on; [|exact Hag]. split; [reflexivity | exact HF].
Qed.

(* A [rule.impl] derives [nf] exactly when some context interprets all its hypothesis clauses to
   [hyps'] and one conclusion clause to [nf]. *)
Lemma lrule_impl_iff (concls hyps : list lowered_fact)
    (nf : normal_fact) (hyps' : list (Datalog.fact (_rel := rel_id))) :
  rule.interp (Datalog.rule.impl concls hyps) nf hyps' <->
  exists ctx,
    Forall2 (interp_fact ctx) hyps hyps' /\
    Exists (fun c => clause.interp ctx c nf) concls.
Proof.
  split.
  - intros H. inversion H; subst. exists ctx. split; [apply Forall2_interp_fact; eauto | assumption].
  - intros [ctx [Hfa Hex]].
    apply Forall2_interp_fact in Hfa. destruct Hfa as [nhyps [-> Hfa]].
    apply rule.interp_impl with (ctx := ctx); assumption.
Qed.

(*----The bare-variable fragment----*)

Definition bare_fact (lf : lowered_fact) : Prop :=
  Forall (fun e => exists v, e = expr.var v) lf.(Datalog.clause.args).

(* The compiler only produces [rule.impl]s; a rule is *bare* when all its clause arguments
   are bare variables. *)
Definition bare_rule (lr : lowered_rule) : Prop :=
  match lr with
  | Datalog.rule.impl concls hyps => Forall bare_fact hyps /\ Forall bare_fact concls
  | _ => False
  end.

(* For a bare fact, [compute_var_order] (which drops function args) keeps every argument, so
   its length is the fact's arity and arg positions line up with variable positions. *)
Lemma bare_compute_var_order_length (lf : lowered_fact) :
  bare_fact lf -> length (compute_var_order lf) = length lf.(Datalog.clause.args).
Proof.
  unfold bare_fact, DistributedDatalogToHardwareCompiler.compute_var_order. intros H.
  induction lf.(Datalog.clause.args) as [|a args IH]; simpl in *.
  - reflexivity.
  - inversion H as [|x l [v Hv] H']; subst. simpl. rewrite IH; auto.
Qed.

(*----generate_query: shape lemmas (proved)----*)

(* One join per variable in the ordering. *)
Lemma generate_query_length (tb : list trie) (ord : list exprvar) (hyps : list lowered_fact) :
  length (generate_query tb ord hyps) = length ord.
Proof. unfold DistributedDatalogToHardwareCompiler.generate_query. apply length_map. Qed.

(* The i-th join is the join for the i-th variable in the ordering (default-free form). *)
Lemma generate_query_nth_error (tb : list trie) (ord : list exprvar)
    (hyps : list lowered_fact) (i : nat) :
  nth_error (generate_query tb ord hyps) i
  = option_map (fun v => generate_join tb v hyps) (nth_error ord i).
Proof. unfold DistributedDatalogToHardwareCompiler.generate_query. apply nth_error_map. Qed.

(*----Binding <-> context----*)

(* A binding [vals] over a [NoDup] ordering [ord] induces the datalog context that the lowered
   rule is evaluated under: position [i] in the ordering is variable [nth i ord], holding value
   [nth i vals]. *)
Definition ctx_of (ord : list exprvar) (vals : list value) : option context :=
  map.of_list_zip ord vals.

(* The induced context exists whenever the binding has one value per ordering slot. *)
Lemma ctx_of_exists (ord : list exprvar) (vals : list value) :
  length ord = length vals -> exists ctx, ctx_of ord vals = Some ctx.
Proof.
  intros H. unfold ctx_of, map.of_list_zip.
  apply (map.sameLength_putmany_of_list ord vals map.empty H).
Qed.

(* And it maps the i-th ordering variable to the i-th value (ordering is duplicate-free). *)
Lemma ctx_of_get (ord : list exprvar) (vals : list value) (ctx : context) (i : nat) (v : exprvar) (t : value) :
  NoDup ord ->
  ctx_of ord vals = Some ctx ->
  nth_error ord i = Some v ->
  nth_error vals i = Some t ->
  map.get ctx v = Some t.
Proof.
  intros Hnd Hctx Hi Hv. unfold ctx_of, map.of_list_zip in Hctx.
  eapply (map.putmany_of_list_zip_get_newval
            (key_eqb := var_eqb) (key_eq_dec := Eqb_ok_BoolSpec)); eauto.
Qed.

(*----join_output_fact: projection characterization (proved)----*)

(* The inner fold of [join_output_fact] succeeds with [out] iff every index reads its value. *)
Lemma project_vals_ok (vals : list value) (idxs : list nat) (out : list value) :
  fold_right (fun idx acc =>
    match acc, nth_error vals idx with
    | Some vs, Some v => Some (v :: vs)
    | _, _ => None
    end) (Some []) idxs = Some out
  <-> Forall2 (fun idx v => nth_error vals idx = Some v) idxs out.
Proof.
  revert out. induction idxs as [|idx idxs IH]; intros out; simpl.
  - split; intros H; [injection H as <-; constructor | inversion H; reflexivity].
  - split.
    + intros H.
      destruct (fold_right _ (Some []) idxs) as [vs|] eqn:E;
        destruct (nth_error vals idx) as [v|] eqn:Ev; try discriminate.
      injection H as <-. constructor; [exact Ev | apply IH; reflexivity].
    + intros H. inversion H as [|idx0 v idxs0 out0 Hv Hrest Heq1 Heq2]; subst.
      apply IH in Hrest. rewrite Hrest, Hv. reflexivity.
Qed.

(* Hence the whole [join_output_fact] in terms of the projected tuple. *)
Lemma join_output_fact_spec (vals : list value) (jo : join_output) (nf : normal_fact) :
  join_output_fact vals jo = Some nf
  <-> exists out, nf = {| normal_fact.rel := jo.(output_rel); normal_fact.args := out |} /\
                  Forall2 (fun idx v => nth_error vals idx = Some v)
                          jo.(output_var_indices) out.
Proof.
  unfold join_output_fact.
  destruct (fold_right _ (Some []) jo.(output_var_indices)) as [out|] eqn:E.
  - split.
    + intros H; injection H as <-. exists out. split; [reflexivity | apply project_vals_ok; exact E].
    + intros [out' [Hf Hfa]]. apply project_vals_ok in Hfa.
      rewrite Hfa in E. injection E as <-. rewrite Hf. reflexivity.
  - split; [discriminate|].
    intros [out' [Hf Hfa]]. apply project_vals_ok in Hfa. rewrite Hfa in E. discriminate.
Qed.

(*----Conclusion projection: join_output_fact <-> clause.interp (bare concls)----*)

Lemma interp_var_iff (ctx : context) (v : exprvar) (x : value) :
  expr.interp ctx (expr.var v : Datalog.expr (_fn := fn)) x <-> map.get ctx v = Some x.
Proof.
  split.
  - intros H; inversion H; subst; assumption.
  - intros H; constructor; assumption.
Qed.

(* The induced context reads the i-th ordering variable as the i-th binding value. *)
Lemma ctx_get_eq_nth (ord : list exprvar) (vals : list value) (ctx : context) (idx : nat) (v : exprvar) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  nth_error ord idx = Some v ->
  map.get ctx v = nth_error vals idx.
Proof.
  intros Hnd Hlen Hctx Hord.
  assert (Hlt : idx < length ord) by (apply nth_error_Some; congruence).
  destruct (nth_error vals idx) as [t|] eqn:Ev.
  - eapply ctx_of_get; eauto.
  - apply nth_error_None in Ev. lia.
Qed.

(* Bare conclusion args paired with their ordering indices: interpreting the args under the
   induced context yields exactly the values the indices project from the binding. *)
Lemma corr_bridge (ord : list exprvar) (vals : list value) (ctx : context) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  forall args idxs out,
  Forall2 (fun e idx => exists v, e = expr.var v /\ nth_error ord idx = Some v) args idxs ->
  ( Forall2 (expr.interp ctx) (args) out
    <-> Forall2 (fun idx v => nth_error vals idx = Some v) idxs out ).
Proof.
  intros Hnd Hlen Hctx args idxs out Hcorr. revert out.
  induction Hcorr as [| e idx args idxs [v [He Hov]] Hc IH]; intros out; subst.
  - simpl. split; intros H; inversion H; constructor.
  - simpl. split.
    + intros H. inversion H as [|e0 x args0 out0 Hx Hrest]; subst.
      constructor.
      * apply interp_var_iff in Hx.
        rewrite (ctx_get_eq_nth ord vals ctx idx v Hnd Hlen Hctx Hov) in Hx. exact Hx.
      * apply IH; exact Hrest.
    + intros H. inversion H as [|idx0 x idxs0 out0 Hx Hrest]; subst.
      constructor.
      * apply interp_var_iff.
        rewrite (ctx_get_eq_nth ord vals ctx idx v Hnd Hlen Hctx Hov). exact Hx.
      * apply IH; exact Hrest.
Qed.

(* The conclusion side, fully connected: the trie-join's output equals the lowered rule's
   conclusion fact under the induced context.  [Hcorr] is the structural fact that
   [compile_concl] establishes for bare conclusions (each output index is the ordering
   index of the corresponding variable). *)
Lemma join_output_fact_interp (concl : lowered_fact) (ord : list exprvar) (vals : list value)
    (ctx : context) (jo : join_output) (nf : normal_fact) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  jo.(output_rel) = concl.(Datalog.clause.rel) ->
  Forall2 (fun e idx => exists v, e = expr.var v /\ nth_error ord idx = Some v)
          concl.(Datalog.clause.args) jo.(output_var_indices) ->
  ( join_output_fact vals jo = Some nf <-> clause.interp ctx concl nf ).
Proof.
  intros Hnd Hlen Hctx Hrel Hcorr. rewrite join_output_fact_spec. split.
  - intros [out [-> Hfa]]. split; [symmetry; exact Hrel|].
    apply (corr_bridge ord vals ctx Hnd Hlen Hctx _ _ _ Hcorr). exact Hfa.
  - intros [Hr Hfa]. exists nf.(normal_fact.args). split.
    + destruct nf as [R args]. simpl in *. congruence.
    + apply (corr_bridge ord vals ctx Hnd Hlen Hctx _ _ _ Hcorr). exact Hfa.
Qed.

(*============================================================================*)
(*  compute_permutation is a NoDup permutation list of the right length        *)
(*============================================================================*)

Abbreviation cperm_aux := (@DistributedDatalogToHardwareCompiler.compute_perm_aux exprvar var_idx_map).
Abbreviation cperm := (@DistributedDatalogToHardwareCompiler.compute_permutation exprvar var_eqb var_idx_map).
Abbreviation bbm := (@DistributedDatalogToHardwareCompiler.build_base_map exprvar var_eqb var_idx_map).

Definition mget0 (m : var_idx_map) (v : exprvar) : nat :=
  match map.get m v with Some n => n | None => 0 end.

Lemma var_eqb_refl (v : exprvar) : var_eqb v v = true.
Proof. destruct (Eqb_ok_BoolSpec v v); congruence. Qed.

(*----count_occ / firstn helpers----*)

Lemma count_occ_nil (q : exprvar) : count_occ q [] = 0.
Proof. reflexivity. Qed.

Lemma count_occ_cons (q x : exprvar) (l : list exprvar) :
  count_occ q (x :: l) = (if var_eqb x q then 1 else 0) + count_occ q l.
Proof.
  unfold count_occ. cbn [filter].
  rewrite (Eqb.eqb_sym q x : var_eqb q x = var_eqb x q).
  destruct (var_eqb x q); reflexivity.
Qed.

Lemma firstn_S_nth (l : list exprvar) (i : nat) (d : exprvar) :
  i < length l -> firstn (S i) l = firstn i l ++ [nth i l d].
Proof.
  revert i. induction l as [|x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [|i']; simpl; [reflexivity|].
    rewrite (IH i') by lia. reflexivity.
Qed.

Lemma count_occ_firstn_S (v : exprvar) (l : list exprvar) (i : nat) (d : exprvar) :
  i < length l ->
  count_occ v (firstn (S i) l) = count_occ v (firstn i l) + (if var_eqb (nth i l d) v then 1 else 0).
Proof.
  intros Hi. rewrite (firstn_S_nth l i d Hi), count_occ_app, count_occ_cons, count_occ_nil.
  lia.
Qed.

Lemma count_firstn_mono (v : exprvar) (l : list exprvar) (i j : nat) :
  i <= j -> count_occ v (firstn i l) <= count_occ v (firstn j l).
Proof.
  intros Hij. induction Hij as [|j Hij IH]; [lia|].
  destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
  - rewrite (count_occ_firstn_S v l j v Hlt). lia.
  - rewrite (firstn_all2 (n := S j) l) by lia.
    rewrite (firstn_all2 (n := j) l) in IH by lia. lia.
Qed.

Lemma count_firstn_strict (v : exprvar) (l : list exprvar) (i j : nat) (d : exprvar) :
  i < j -> nth i l d = v -> i < length l ->
  count_occ v (firstn i l) < count_occ v (firstn j l).
Proof.
  intros Hij Hnth Hi.
  apply Nat.lt_le_trans with (m := count_occ v (firstn (S i) l)).
  - rewrite (count_occ_firstn_S v l i d Hi), Hnth, var_eqb_refl. lia.
  - apply count_firstn_mono. lia.
Qed.

(* Occurrence index of position i is strictly below the total count of that variable. *)
Lemma occ_lt_count (v : exprvar) (l : list exprvar) (i : nat) (d : exprvar) :
  i < length l -> nth i l d = v ->
  count_occ v (firstn i l) < count_occ v l.
Proof.
  intros Hi Hnth.
  assert (H1 : count_occ v (firstn (S i) l) = count_occ v (firstn i l) + 1).
  { rewrite (count_occ_firstn_S v l i d Hi), Hnth, var_eqb_refl. lia. }
  assert (H2 : count_occ v (firstn (S i) l) <= count_occ v (firstn (length l) l)).
  { apply count_firstn_mono. lia. }
  rewrite firstn_all in H2. lia.
Qed.

(*----length and value characterization of compute_perm_aux----*)

Lemma cperm_aux_length (l : list exprvar) (bm om : var_idx_map) :
  length (cperm_aux l bm om) = length l.
Proof. revert om. induction l as [|v vs IH]; intros om; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma cperm_aux_cons (v : exprvar) (vs : list exprvar) (bm om : var_idx_map) :
  cperm_aux (v :: vs) bm om
  = (mget0 bm v + mget0 om v) :: cperm_aux vs bm (map.put om v (mget0 om v + 1)).
Proof. reflexivity. Qed.

Lemma mget0_put_same (m : var_idx_map) (v : exprvar) (n : nat) :
  mget0 (map.put m v n) v = n.
Proof. unfold mget0. rewrite map.get_put_same. reflexivity. Qed.

Lemma mget0_put_diff (m : var_idx_map) (v w : exprvar) (n : nat) :
  v <> w -> mget0 (map.put m v n) w = mget0 m w.
Proof. intros H. unfold mget0. rewrite map.get_put_diff by congruence. reflexivity. Qed.

(* nth value produced for position i: base of its variable, plus how many times that variable
   already occurred (in [om] and in the prefix consumed so far). *)
Lemma cperm_aux_nth (bm : var_idx_map) (l : list exprvar) :
  forall (om : var_idx_map) (i : nat) (d : exprvar),
  i < length l ->
  nth i (cperm_aux l bm om) 0 =
    mget0 bm (nth i l d) + mget0 om (nth i l d) + count_occ (nth i l d) (firstn i l).
Proof.
  induction l as [|v vs IH]; intros om i d Hi; simpl in Hi; [lia|].
  rewrite cperm_aux_cons. destruct i as [|i'].
  - cbn [nth firstn]. rewrite count_occ_nil. lia.
  - cbn [nth]. rewrite (IH (map.put om v (mget0 om v + 1)) i' d) by lia.
    change (firstn (S i') (v :: vs)) with (v :: firstn i' vs).
    rewrite (count_occ_cons (nth i' vs d) v (firstn i' vs)).
    destruct (Eqb_ok_BoolSpec v (nth i' vs d)) as [Heq|Hne].
    + change (if true then 1 else 0) with 1. rewrite Heq, mget0_put_same. lia.
    + change (if false then 1 else 0) with 0.
      rewrite (mget0_put_diff om v (nth i' vs d) (mget0 om v + 1) Hne). lia.
Qed.

(*----base offsets assigned by build_base_map----*)

(* The offset build_base_map assigns to v's first occurrence in [desired]. *)
Fixpoint base_fn (desired original : list exprvar) (offset : nat) (v : exprvar) : nat :=
  match desired with
  | [] => offset
  | w :: ws => if var_eqb w v then offset
               else base_fn ws original (offset + count_occ w original) v
  end.

Lemma base_fn_ge (desired original : list exprvar) (offset : nat) (v : exprvar) :
  offset <= base_fn desired original offset v.
Proof.
  revert offset. induction desired as [|w ws IH]; intros offset; simpl; [lia|].
  destruct (var_eqb w v); [lia|]. specialize (IH (offset + count_occ w original)). lia.
Qed.

Lemma bbm_cons (w : exprvar) (ws original : list exprvar) (offset : nat) (m : var_idx_map) :
  bbm (w :: ws) original offset m
  = bbm ws original (offset + count_occ w original) (map.put m w offset).
Proof. reflexivity. Qed.

Lemma build_base_map_get_notin (desired original : list exprvar) (offset : nat)
    (m : var_idx_map) (v : exprvar) :
  ~ In v desired -> map.get (bbm desired original offset m) v = map.get m v.
Proof.
  revert offset m. induction desired as [|w ws IH]; intros offset m Hnin; [reflexivity|].
  rewrite bbm_cons, IH by (simpl in Hnin; tauto).
  rewrite map.get_put_diff by (simpl in Hnin; intuition congruence). reflexivity.
Qed.

Lemma build_base_map_get (desired original : list exprvar) (offset : nat)
    (m : var_idx_map) (v : exprvar) :
  NoDup desired -> In v desired ->
  map.get (bbm desired original offset m) v = Some (base_fn desired original offset v).
Proof.
  revert offset m. induction desired as [|w ws IH]; intros offset m Hnd Hin;
    simpl in Hin; [contradiction|].
  rewrite bbm_cons. inversion Hnd as [|x l Hwnin Hnd' Heqd]; subst.
  cbn [base_fn]. destruct (Eqb_ok_BoolSpec w v) as [Heq|Hne].
  - subst w. rewrite build_base_map_get_notin by exact Hwnin.
    rewrite map.get_put_same. reflexivity.
  - destruct Hin as [Hwv|Hin']; [congruence|]. apply IH; assumption.
Qed.

(* Distinct variables get disjoint blocks [base, base+count): one block lies entirely below
   the other. *)
Lemma base_fn_mono (desired original : list exprvar) (offset : nat) (v w : exprvar) :
  NoDup desired -> In v desired -> In w desired -> v <> w ->
  base_fn desired original offset v + count_occ v original <= base_fn desired original offset w
  \/ base_fn desired original offset w + count_occ w original <= base_fn desired original offset v.
Proof.
  revert offset. induction desired as [|u us IH]; intros offset Hnd Hv Hw Hvw;
    simpl in Hv, Hw; [contradiction|].
  inversion Hnd as [|x l Hunin Hnd' Heqd]; subst.
  cbn [base_fn].
  destruct (Eqb_ok_BoolSpec u v) as [Huv|Huv]; destruct (Eqb_ok_BoolSpec u w) as [Huw|Huw].
  - congruence.
  - subst u. destruct Hw as [Hwv|Hwin]; [congruence|].
    left. pose proof (base_fn_ge us original (offset + count_occ v original) w). lia.
  - subst u. destruct Hv as [Hvu|Hvin]; [congruence|].
    right. pose proof (base_fn_ge us original (offset + count_occ w original) v). lia.
  - destruct Hv as [Hvu|Hvin]; [congruence|]. destruct Hw as [Hwu|Hwin]; [congruence|].
    apply (IH (offset + count_occ u original) Hnd' Hvin Hwin Hvw).
Qed.

(*----compute_permutation: length, value, NoDup----*)

Lemma mget0_empty (v : exprvar) : mget0 map.empty v = 0.
Proof. unfold mget0. rewrite map.get_empty. reflexivity. Qed.

Lemma compute_permutation_length (original desired : list exprvar) :
  length (cperm original desired) = length original.
Proof. unfold DistributedDatalogToHardwareCompiler.compute_permutation. apply cperm_aux_length. Qed.

Lemma compute_permutation_nth (original desired : list exprvar) (i : nat) (d : exprvar) :
  i < length original ->
  nth i (cperm original desired) 0 =
    mget0 (bbm desired original 0 map.empty) (nth i original d)
      + count_occ (nth i original d) (firstn i original).
Proof.
  intros Hi. unfold DistributedDatalogToHardwareCompiler.compute_permutation.
  rewrite (cperm_aux_nth (bbm desired original 0 map.empty) original map.empty i d Hi).
  rewrite mget0_empty. lia.
Qed.

(* The value at position i is [base(vi) + occ_i] with [occ_i < count vi]; distinct positions
   thus get distinct values. *)
Lemma cperm_val_neq (original desired : list exprvar) (d : exprvar) (i j : nat) :
  NoDup desired -> (forall v, In v original -> In v desired) ->
  i < j -> j < length original ->
  nth i (cperm original desired) 0 <> nth j (cperm original desired) 0.
Proof.
  intros Hnd Hcov Hij Hj.
  assert (Hi : i < length original) by lia.
  pose (vi := nth i original d). pose (vj := nth j original d).
  assert (Hivd : In vi desired) by (apply Hcov; apply nth_In; lia).
  assert (Hjvd : In vj desired) by (apply Hcov; apply nth_In; lia).
  rewrite (compute_permutation_nth original desired i d Hi).
  rewrite (compute_permutation_nth original desired j d Hj).
  fold vi vj.
  assert (Hbi : mget0 (bbm desired original 0 map.empty) vi = base_fn desired original 0 vi)
    by (unfold mget0; rewrite (build_base_map_get desired original 0 map.empty vi Hnd Hivd); reflexivity).
  assert (Hbj : mget0 (bbm desired original 0 map.empty) vj = base_fn desired original 0 vj)
    by (unfold mget0; rewrite (build_base_map_get desired original 0 map.empty vj Hnd Hjvd); reflexivity).
  rewrite Hbi, Hbj.
  pose proof (occ_lt_count vi original i d Hi eq_refl) as Hoi.
  pose proof (occ_lt_count vj original j d Hj eq_refl) as Hoj.
  destruct (Eqb_ok_BoolSpec vi vj) as [Hvv|Hvv].
  - (* same variable: strict growth of occurrence count *)
    rewrite <- Hvv.
    pose proof (count_firstn_strict vi original i j d Hij eq_refl Hi) as Hgrow. lia.
  - destruct (base_fn_mono desired original 0 vi vj Hnd Hivd Hjvd Hvv) as [Hle|Hle]; lia.
Qed.

Lemma compute_permutation_NoDup (original desired : list exprvar) :
  NoDup desired -> (forall v, In v original -> In v desired) ->
  NoDup (cperm original desired).
Proof.
  intros Hnd Hcov. destruct original as [|d0 orig'] eqn:Eo.
  - unfold DistributedDatalogToHardwareCompiler.compute_permutation. simpl. constructor.
  - apply (proj2 (NoDup_nth (cperm (d0 :: orig') desired) 0)).
    intros i j Hi Hj Heq.
    rewrite compute_permutation_length in Hi, Hj.
    destruct (Nat.lt_trichotomy i j) as [Hlt|[Heqij|Hgt]].
    + exfalso. exact (cperm_val_neq (d0 :: orig') desired d0 i j Hnd Hcov Hlt Hj Heq).
    + exact Heqij.
    + exfalso. exact (cperm_val_neq (d0 :: orig') desired d0 j i Hnd Hcov Hgt Hi (eq_sym Heq)).
Qed.

(*============================================================================*)
(*  Characterizing generate_join's entry list                                  *)
(*============================================================================*)

Lemma map_recombine_triple {X Y Z : Type} (l : list (X * Y * Z)) :
  map (fun e => (fst3 e, snd3 e, thd3 e)) l = l.
Proof. induction l as [|[[x y] z] l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma In_combine3_seq {A B : Type} (la : list A) (lb : list B) (s c : nat) (x : A) (y : B) :
  In (c, x, y) (combine3 (seq s (length lb)) la lb) <->
  (exists k, c = s + k /\ nth_error la k = Some x /\ nth_error lb k = Some y).
Proof.
  revert la s. induction lb as [|b lb IH]; intros la s; simpl.
  - split; [contradiction|]. intros [k [_ [_ Hk]]]. destruct k; discriminate.
  - destruct la as [|a la]; simpl.
    + split; [contradiction|]. intros [k [_ [Hk _]]]. destruct k; discriminate.
    + split.
      * intros [Heq | Hin].
        -- inversion Heq; subst. exists 0. split; [lia | split; reflexivity].
        -- apply IH in Hin. destruct Hin as [k [-> [Hk1 Hk2]]]. exists (S k). split; [lia | split; assumption].
      * intros [k [-> [Hk1 Hk2]]]. destruct k as [|k]; simpl in Hk1, Hk2.
        ++ injection Hk1 as Hx. injection Hk2 as Hy. subst x. subst y. left.
           replace (s + 0) with s by lia. reflexivity.
        ++ right. apply IH. exists k. split; [lia | split; assumption].
Qed.

Lemma combine_nth_error {A B} (l1 : list A) (l2 : list B) c x y :
  nth_error (combine l1 l2) c = Some (x, y) <->
  nth_error l1 c = Some x /\ nth_error l2 c = Some y.
Proof.
  revert l2 c. induction l1 as [|a l1 IH]; intros [|b l2] [|c]; simpl;
    try (split; [discriminate | intros [H _]; discriminate]);
    try (split; [discriminate | intros [_ H]; discriminate]).
  - split; [intros H; injection H as -> ->; auto | intros [H1 H2]; injection H1 as ->; injection H2 as ->; reflexivity].
  - apply IH.
Qed.

Lemma zip3_map3 {A X Y Z : Type} (f : A -> X) (g : A -> Y) (h : A -> Z) (l : list A) :
  zip3 (map f l) (map g l) (map h l) = map (fun a => (f a, g a, h a)) l.
Proof. induction l as [|x l IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

(* The flat list of entries generate_join produces (forward order). *)
Definition gj_entries (tb : list trie) (v : exprvar) (hyps : list lowered_fact)
  : list (trie_id * nat * clause_id) :=
  flat_map (fun '(c, t, hyp) =>
              map (fun a => (t.(tid), nth a t.(tperm) 0, c))
                  (indexes_of (expr.var v) hyp.(Datalog.clause.args)))
           (combine3 (seq 0 (length hyps)) tb hyps).

Lemma generate_join_entries (tb : list trie) (v : exprvar) (hyps : list lowered_fact) :
  zip3 (generate_join tb v hyps).(HardwareProgram.tries)
       (generate_join tb v hyps).(trie_levels)
       (generate_join tb v hyps).(clauses)
  = gj_entries tb v hyps.
Proof.
  unfold DistributedDatalogToHardwareCompiler.generate_join, gj_entries.
  cbn [tries trie_levels clauses].
  rewrite zip3_map3. apply map_recombine_triple.
Qed.

(*----helpers for the generic-join correctness----*)

Lemma Forall2_nth_error_iff {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) :
  Forall2 P l1 l2 <->
  (length l1 = length l2 /\
   forall i x y, nth_error l1 i = Some x -> nth_error l2 i = Some y -> P x y).
Proof.
  split.
  - intros H. induction H as [|x y l1 l2 Hxy HF IH].
    + split; [reflexivity|]. intros [|i]; discriminate.
    + destruct IH as [Hlen IHn]. split; [simpl; congruence|].
      intros [|i] x0 y0; simpl; intros Hx Hy.
      * injection Hx as <-. injection Hy as <-. exact Hxy.
      * eapply IHn; eauto.
  - revert l2. induction l1 as [|x l1 IH]; intros l2 [Hlen Hn].
    + destruct l2; [constructor | discriminate].
    + destruct l2 as [|y l2]; [discriminate|]. constructor.
      * apply (Hn 0 x y); reflexivity.
      * apply IH. split; [simpl in Hlen; congruence|].
        intros i x0 y0 Hx Hy. apply (Hn (S i) x0 y0); assumption.
Qed.

(* Membership in an "enumerate": [combine (seq s n) l] with [n = length l]. *)
Lemma In_combine_seq {A : Type} (l : list A) (s c : nat) (x : A) :
  In (c, x) (combine (seq s (length l)) l) <->
  (exists k, c = s + k /\ nth_error l k = Some x).
Proof.
  revert s. induction l as [|a l IH]; intros s; simpl.
  - split; [contradiction|]. intros [k [_ Hk]]. destruct k; discriminate.
  - split.
    + intros [Heq | Hin].
      * inversion Heq; subst. exists 0. split; [lia | reflexivity].
      * apply IH in Hin. destruct Hin as [k [-> Hk]]. exists (S k). split; [lia | exact Hk].
    + intros [k [-> Hk]]. destruct k as [|k]; simpl in Hk.
      * injection Hk as <-. left. f_equal; lia.
      * right. apply IH. exists k. split; [lia | exact Hk].
Qed.

(* Membership in generate_join's entry list. *)
Lemma gj_entries_In (tb : list trie) (v : exprvar) (hyps : list lowered_fact)
    (e : trie_id * nat * clause_id) :
  In e (gj_entries tb v hyps) <->
  (exists c t hyp a,
     nth_error (combine tb hyps) c = Some (t, hyp) /\
     nth_error hyp.(Datalog.clause.args) a = Some (expr.var v) /\
     e = (t.(tid), nth a t.(tperm) 0, c)).
Proof.
  unfold gj_entries. rewrite in_flat_map. split.
  - intros [[[c t] hyp] [Hin Hin2]].
    apply In_combine3_seq in Hin. destruct Hin as [k [Hck [Htk Hhk]]]. simpl in Hck; subst c.
    apply in_map_iff in Hin2. destruct Hin2 as [a [He Ha]].
    apply indexes_of_spec in Ha.
    exists k, t, hyp, a. split;
      [apply combine_nth_error; split; assumption | split; [exact Ha | symmetry; exact He]].
  - intros [c [t [hyp [a [Hcomb [Ha ->]]]]]].
    apply combine_nth_error in Hcomb. destruct Hcomb as [Htc Hhc].
    exists (c, t, hyp). split.
    + apply In_combine3_seq. exists c. split; [lia | split; assumption].
    + apply in_map_iff. exists a. split; [reflexivity|].
      apply indexes_of_spec. exact Ha.
Qed.

(* Reading a lowered fact as a datalog fact, factored. *)
Lemma interp_lfact_iff (ctx : context) (lf : lowered_fact) (R : rel_id) (tup : list value) :
  interp_fact ctx lf (nfact R tup) <->
  R = lf.(Datalog.clause.rel) /\ Forall2 (expr.interp ctx) (lf.(Datalog.clause.args)) tup.
Proof.
  split.
  - intros [nf_args [HF Heq]]. injection Heq as HR Htup. subst. split; [reflexivity | assumption].
  - intros [HR HF]. subst R. exists tup. split; [exact HF | reflexivity].
Qed.

(* For bare args, the per-position interpretation condition. *)
Lemma bare_interp_args_iff (ctx : context)
    (args : list (@HardwareProgram.lowered_expr exprvar fn)) (tup : list value) :
  Forall (fun e => exists v, e = expr.var v) args ->
  ( Forall2 (expr.interp ctx) (args) tup <->
    (length args = length tup /\
     forall a w, nth_error args a = Some (expr.var w) -> nth_error tup a = map.get ctx w) ).
Proof.
  intros Hbare. rewrite Forall2_nth_error_iff. split.
  - intros [Hlen Hpt]. split; [exact Hlen|]. intros a w Haw.
    assert (Hargs : a < length args).
    { apply (proj1 (nth_error_Some args a)). rewrite Haw. discriminate. }
    assert (Hat : nth_error tup a <> None).
    { apply (proj2 (nth_error_Some tup a)). rewrite <- Hlen. exact Hargs. }
    destruct (nth_error tup a) as [y|] eqn:Hy; [|congruence].
    specialize (Hpt a _ _ Haw Hy). apply interp_var_iff in Hpt. symmetry; exact Hpt.
  - intros [Hlen Hpt]. split; [exact Hlen|]. intros a arg y Earg Hy.
    assert (Hw : exists w, arg = expr.var w)
      by (rewrite Forall_forall in Hbare; apply Hbare; eapply nth_error_In; exact Earg).
    destruct Hw as [w ->]. apply interp_var_iff.
    specialize (Hpt a w Earg). rewrite Hy in Hpt. symmetry; exact Hpt.
Qed.

(*============================================================================*)
(*  Core obligation: generic-join correctness (bare fragment)                 *)
(*============================================================================*)

(* The trie-join [generate_query tb ord hyps] admits binding [vals] (against the global trie
   table [tries] and hypothesis tuples [hyps']) exactly when the induced context interprets
   every (renamed) hypothesis to the corresponding tuple.

   Structural preconditions [Htb] capture what the *fixed* [compile_hyps] guarantees: the i-th
   per-hyp trie indexes the i-th hypothesis's relation with the permutation computed for that
   hypothesis, and is registered in the table.  This is the heart of the proof; the index
   bookkeeping is discharged by [trie_read_NoDup] (already proved in NodeHardwareSemantics) once the
   permutation is shown to be [NoDup].

   Proof sketch (both directions):
   - (->) Given satisfying [vals], take [ctx := ctx_of ord vals].  For hypothesis i with bare
     args, [join_sat] for each variable position forces [nth (pos of v in ord) vals] to equal
     [trie_read tperm_i tup_i level]; [trie_read_NoDup] rewrites that to [nth_error tup_i argpos],
     which is exactly [expr.interp ctx (expr.var v)].  Assemble [interp_fact ctx (h_i) (..)].
   - (<-) Given [ctx] interpreting all hyps, read [vals := map (ctx) ord]; each join entry reads
     back the matching tuple column by the same [trie_read_NoDup] identity. *)
Theorem generate_query_correct
    (ord : list exprvar) (hyps : list lowered_fact) (tb : list trie) (tries : list trie)
    (vals : list value) (hyps' : list (Datalog.fact (_rel := rel_id))) (dt : trie) (dh : lowered_fact) :
  NoDup ord ->
  Forall bare_fact hyps ->
  length tb = length hyps ->
  length hyps' = length hyps ->
  length vals = length ord ->
  (forall v, In v (flat_map compute_var_order hyps) -> In v ord) ->
  (forall i, i < length hyps ->
     (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause.rel) /\
     (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
                                (compute_var_order (nth i hyps dh)) ord /\
     lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
     exists tup, nth i hyps' (nfact 0 []) =
                   nfact (nth i hyps dh).(Datalog.clause.rel) tup /\
                 length tup = length (nth i hyps dh).(Datalog.clause.args)) ->
  ( query_sat tries (generate_query tb ord hyps) vals hyps'
    <-> exists ctx, ctx_of ord vals = Some ctx /\
                    Forall2 (interp_fact ctx) (hyps) hyps' ).
Proof.
  intros Hnd Hbare Htbl Hhl Hvl Hcov Hstruct.
  destruct (ctx_of_exists ord vals (eq_sym Hvl)) as [ctx Hctx].
  assert (Hcomb : forall c, c < length hyps ->
            nth_error (combine tb hyps) c = Some (nth c tb dt, nth c hyps dh)).
  { intros c Hc. rewrite (nth_error_nth' _ (dt, dh)) by (rewrite length_combine; lia).
    rewrite combine_nth by lia. reflexivity. }
  assert (Hcombinv : forall c t hyp, nth_error (combine tb hyps) c = Some (t, hyp) ->
            c < length hyps /\ t = nth c tb dt /\ hyp = nth c hyps dh).
  { intros c t hyp H. assert (Hc : c < length hyps).
    { assert (Hne : nth_error (combine tb hyps) c <> None) by (rewrite H; discriminate).
      apply nth_error_Some in Hne. rewrite length_combine in Hne. lia. }
    rewrite Hcomb in H by lia. injection H as <- <-. auto. }
  (* per-(c,a) bridge: a join entry holds iff the c-th tuple's a-th column is the value *)
  assert (Hentry : forall c a w u tupc,
            c < length hyps ->
            nth c hyps' (nfact 0 []) =
              nfact (nth c hyps dh).(Datalog.clause.rel) tupc ->
            nth_error (nth c hyps dh).(Datalog.clause.args) a = Some (expr.var w) ->
            ( join_entry_sat tries hyps' u ((nth c tb dt).(tid), nth a (nth c tb dt).(tperm) 0, c)
              <-> nth_error tupc a = Some u )).
  { intros c a w u tupc Hc Hnf Haw.
    destruct (Hstruct c Hc) as [Htrel [Htperm [Hlook [tup0 [Hnf0 Hltup]]]]].
    rewrite Hnf0 in Hnf. injection Hnf as Htup. subst tup0.
    assert (Hbarec : bare_fact (nth c hyps dh))
      by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
    assert (Hnodupp : NoDup (nth c tb dt).(tperm)).
    { rewrite Htperm. apply compute_permutation_NoDup; [exact Hnd|].
      intros v Hv. apply Hcov, in_flat_map.
      exists (nth c hyps dh). split; [apply nth_In; lia | exact Hv]. }
    assert (Halt : a < length (nth c hyps dh).(Datalog.clause.args)) by (apply nth_error_Some; congruence).
    assert (Harity : a < length (nth c tb dt).(tperm)).
    { rewrite Htperm, compute_permutation_length, bare_compute_var_order_length by exact Hbarec.
      exact Halt. }
    assert (Hnh : nth_error hyps' c = Some (nfact (nth c hyps dh).(Datalog.clause.rel) tupc)).
    { rewrite (nth_error_nth' hyps' (nfact 0 [])) by lia. rewrite Hnf0. reflexivity. }
    unfold join_entry_sat. split.
    - intros [t' [tup' [Hl' [Hn' Hr]]]].
      rewrite Hlook in Hl'. injection Hl' as <-.
      rewrite Hnh in Hn'. rewrite Htrel in Hn'. injection Hn' as Hn'.
      rewrite (trie_read_NoDup _ _ a Hnodupp Harity) in Hr.
      rewrite Hn'. exact Hr.
    - intros Ht.
      exists (nth c tb dt), tupc.
      split; [exact Hlook | split].
      + rewrite Hnh. rewrite Htrel. reflexivity.
      + rewrite (trie_read_NoDup _ _ a Hnodupp Harity). exact Ht. }
  (* query_sat reduced to a per-(ordering-position) form *)
  assert (Hqs : query_sat tries (generate_query tb ord hyps) vals hyps' <->
    (forall i v, nth_error ord i = Some v ->
       exists vi, nth_error vals i = Some vi /\
         forall e, In e (gj_entries tb v hyps) -> join_entry_sat tries hyps' vi e)).
  { unfold query_sat. split.
    - intros [_ HF] i v Hiv. rewrite Forall_forall in HF.
      assert (Hin : In (i, generate_join tb v hyps)
        (combine (seq 0 (length (generate_query tb ord hyps))) (generate_query tb ord hyps))).
      { apply In_combine_seq. exists i. split; [lia|].
        rewrite generate_query_nth_error, Hiv. reflexivity. }
      specialize (HF _ Hin). simpl in HF. destruct HF as [vi [Hvi HFe]].
      exists vi. split; [exact Hvi|]. rewrite <- generate_join_entries, <- Forall_forall. exact HFe.
    - intros H. split.
      + rewrite generate_query_length. exact Hvl.
      + rewrite Forall_forall. intros [i j] Hin.
        apply In_combine_seq in Hin. destruct Hin as [k [Hik Hk]]. simpl in Hik; subst i.
        rewrite generate_query_nth_error in Hk.
        destruct (nth_error ord k) as [v|] eqn:Hov2; simpl in Hk; [|discriminate].
        injection Hk as <-. simpl. specialize (H k v Hov2). destruct H as [vi [Hvi HFe]].
        exists vi. split; [exact Hvi|]. rewrite generate_join_entries, Forall_forall. exact HFe. }
  (* the common pointwise condition *)
  pose (Ccond := forall c a w, c < length hyps ->
          nth_error (nth c hyps dh).(Datalog.clause.args) a = Some (expr.var w) ->
          nth_error (nfargs (nth c hyps' (nfact 0 []))) a = map.get ctx w).
  assert (Hq_iff : query_sat tries (generate_query tb ord hyps) vals hyps' <-> Ccond).
  { rewrite Hqs. unfold Ccond. split.
    - intros H c a w Hc Haw.
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      assert (Inw : In w ord).
      { apply Hcov, in_flat_map. exists (nth c hyps dh). split; [apply nth_In; lia|].
        unfold compute_var_order, DistributedDatalogToHardwareCompiler.compute_var_order. apply in_flat_map.
        exists (expr.var w). split; [eapply nth_error_In; exact Haw | simpl; auto]. }
      destruct (In_nth_error _ _ Inw) as [i Hi].
      specialize (H i w Hi). destruct H as [vi [Hvi HFe]].
      assert (Hin_e : In ((nth c tb dt).(tid), nth a (nth c tb dt).(tperm) 0, c) (gj_entries tb w hyps)).
      { apply gj_entries_In. exists c, (nth c tb dt), (nth c hyps dh), a.
        split; [apply Hcomb; lia | split; [exact Haw | reflexivity]]. }
      specialize (HFe _ Hin_e). apply (Hentry c a w vi tupc Hc Hnf Haw) in HFe.
      replace (nfargs (nth c hyps' (nfact 0 []))) with tupc
        by (rewrite Hnf; reflexivity).
      rewrite HFe, (ctx_get_eq_nth ord vals ctx i w Hnd (eq_sym Hvl) Hctx Hi). symmetry; exact Hvi.
    - intros H i v Hiv.
      assert (Hilt : i < length ord) by (apply nth_error_Some; congruence).
      destruct (nth_error vals i) as [vi|] eqn:Hvi; [|exfalso; apply nth_error_None in Hvi; lia].
      exists vi. split; [reflexivity|]. intros e He.
      apply gj_entries_In in He. destruct He as [c [t [hyp [a [Hce [Hae ->]]]]]].
      destruct (Hcombinv _ _ _ Hce) as [Hc [-> ->]].
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      apply (Hentry c a v vi tupc Hc Hnf Hae).
      specialize (H c a v Hc Hae).
      replace (nfargs (nth c hyps' (nfact 0 []))) with tupc in H
        by (rewrite Hnf; reflexivity).
      rewrite H, (ctx_get_eq_nth ord vals ctx i v Hnd (eq_sym Hvl) Hctx Hiv). exact Hvi. }
  assert (Hi_iff : Forall2 (interp_fact ctx) (hyps) hyps' <-> Ccond).
  { rewrite Forall2_nth_error_iff. unfold Ccond. split.
    - intros [Hlen Hpt] c a w Hc Haw.
      assert (Hbarec : bare_fact (nth c hyps dh))
        by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf _]]]]].
      assert (P1 : nth_error (hyps) c = Some ((nth c hyps dh)))
        by (rewrite (nth_error_nth' hyps dh) by lia; reflexivity).
      assert (P2 : nth_error hyps' c =
                     Some (nfact (nth c hyps dh).(Datalog.clause.rel) tupc)).
      { rewrite (nth_error_nth' hyps' (nfact 0 [])) by lia. rewrite Hnf. reflexivity. }
      specialize (Hpt c _ _ P1 P2).
      apply interp_lfact_iff in Hpt. destruct Hpt as [_ HF2].
      apply bare_interp_args_iff in HF2; [|exact Hbarec].
      destruct HF2 as [_ HF2pt].
      replace (nfargs (nth c hyps' (nfact 0 []))) with tupc
        by (rewrite Hnf; reflexivity).
      apply HF2pt; exact Haw.
    - intros H. split; [exact (eq_sym Hhl)|]. intros c xf yf Hxf Hyf.
      change (nth_error hyps c = Some xf) in Hxf.
      assert (Hc : c < length hyps).
      { assert (Hne : nth_error hyps c <> None) by (rewrite Hxf; discriminate).
        apply nth_error_Some in Hne. exact Hne. }
      assert (Exf : nth c hyps dh = xf) by (apply (nth_error_nth hyps c dh); exact Hxf).
      assert (Hbarec : bare_fact (nth c hyps dh))
        by (rewrite Forall_forall in Hbare; apply Hbare; apply nth_In; lia).
      destruct (Hstruct c Hc) as [_ [_ [_ [tupc [Hnf Hltup]]]]].
      assert (Eyf : yf = nfact (nth c hyps dh).(Datalog.clause.rel) tupc).
      { assert (Hyn : nth c hyps' (nfact 0 []) = yf)
          by (apply (nth_error_nth hyps' c (nfact 0 [])); exact Hyf).
        rewrite <- Hyn. exact Hnf. }
      subst xf yf.
      apply interp_lfact_iff. split.
      + reflexivity.
      + apply bare_interp_args_iff; [exact Hbarec|]. split.
        * symmetry; exact Hltup.
        * intros a w Haw. specialize (H c a w Hc Haw).
          replace (nfargs (nth c hyps' (nfact 0 []))) with tupc in H
            by (rewrite Hnf; reflexivity).
          exact H. }
  rewrite Hq_iff. split.
  - intros HC. exists ctx. split; [exact Hctx | apply Hi_iff; exact HC].
  - intros [ctx' [Hctx' Hf]]. assert (ctx' = ctx) by congruence. subst ctx'. apply Hi_iff; exact Hf.
Qed.

(*============================================================================*)
(*  Assembly: a compiled hardware rule matches its lowered rule (bare frag.)  *)
(*============================================================================*)

(* A left element of a [Forall2] has a related right element. *)
Lemma Forall2_In_l {A B : Type} (P : A -> B -> Prop) (l1 : list A) (l2 : list B) (a : A) :
  Forall2 P l1 l2 -> In a l1 -> exists b, In b l2 /\ P a b.
Proof.
  intros HF Hin. induction HF as [|x y l1 l2 Hxy HF IH].
  - inversion Hin.
  - destruct Hin as [-> | Hin].
    + exists y. split; [left; reflexivity | assumption].
    + destruct (IH Hin) as [b [Hbin Hpab]]. exists b. split; [right; assumption | assumption].
Qed.

(* The per-conclusion fact [compile_concl] establishes: the conclusion is bare and each output
   index is the ordering position of the corresponding variable. *)
Definition concl_corr (ord : list exprvar) (c : lowered_fact) (jo : join_output) : Prop :=
  jo.(output_rel) = c.(Datalog.clause.rel) /\
  Forall2 (fun e idx => exists v, e = expr.var v /\ nth_error ord idx = Some v)
          c.(Datalog.clause.args) jo.(output_var_indices).

(* Lifting [join_output_fact_interp] over the whole conclusion list: under the induced context,
   the trie-join's conclusion outputs are exactly the lowered rule's conclusion facts. *)
Lemma concl_exists_iff (ord : list exprvar) (vals : list value) (ctx : context)
    (concls : list lowered_fact) (jos : list join_output) (nf : normal_fact) :
  NoDup ord -> length ord = length vals -> ctx_of ord vals = Some ctx ->
  Forall2 (concl_corr ord) concls jos ->
  ( Exists (fun jo => join_output_fact vals jo = Some nf) jos <->
    Exists (fun c => clause.interp ctx c nf) concls ).
Proof.
  intros Hnd Hlen Hctx HF. induction HF as [| c jo concls jos [Hrel Hcorr] HF IH].
  - simpl. split; intros HE; inversion HE.
  - rewrite !Exists_cons, IH,
      (join_output_fact_interp c ord vals ctx jo nf Hnd Hlen Hctx Hrel Hcorr).
    reflexivity.
Qed.

(* Variables appearing in a corresponding conclusion live in the ordering. *)
Lemma corr_args_vars_in_ord (ord : list exprvar)
    (args : list (@HardwareProgram.lowered_expr exprvar fn)) (idxs : list nat) (v : exprvar) :
  Forall2 (fun e idx => exists w, e = expr.var w /\ nth_error ord idx = Some w) args idxs ->
  In v (flat_map expr.vars (args)) -> In v ord.
Proof.
  intros HF. induction HF as [|e idx args idxs [w [-> Hwo]] HF IH]; simpl; intros Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst v. eapply nth_error_In; exact Hwo.
    + apply IH; exact Hin.
Qed.

(* Transport an [Exists clause.interp] over the conclusion list across two contexts that agree on
   the ordering (the conclusion variables, by [concl_corr], are all in the ordering). *)
Lemma exists_interp_transport (concls : list lowered_fact) (jos : list join_output)
    (ord : list exprvar) (ctx ctx' : context) (nf : normal_fact) :
  Forall2 (concl_corr ord) concls jos ->
  (forall v, In v ord -> map.get ctx v = map.get ctx' v) ->
  Exists (fun c => clause.interp ctx c nf) concls ->
  Exists (fun c => clause.interp ctx' c nf) concls.
Proof.
  intros HF Hag Hex. induction HF as [|c jo concls jos [Hrel Hcorr] HF IH].
  - inversion Hex.
  - rewrite Exists_cons in Hex. rewrite Exists_cons. destruct Hex as [Hc | Hrest].
    + left. eapply clause.interp_agree_on; [exact Hc|].
      apply Forall_forall. intros v Hvin. red. apply Hag.
      eapply (corr_args_vars_in_ord ord c.(Datalog.clause.args) jo.(output_var_indices) v Hcorr). exact Hvin.
    + right. apply IH; exact Hrest.
Qed.

(* A bare hypothesis's datalog variables coincide with its [compute_var_order]. *)
Lemma bare_vars_in_cvo (h : lowered_fact) (v : exprvar) :
  bare_fact h -> In v (Datalog.clause.vars (h)) -> In v (compute_var_order h).
Proof.
  intros Hb Hin.
  assert (Hin' : In v (flat_map expr.vars (h.(Datalog.clause.args)))) by exact Hin.
  apply in_flat_map in Hin'. destruct Hin' as [e [Hein Hve]].
  unfold bare_fact in Hb. rewrite Forall_forall in Hb. destruct (Hb e Hein) as [w Hw]. subst e.
  simpl in Hve. destruct Hve as [Heq | []]. subst v.
  unfold DistributedDatalogToHardwareCompiler.compute_var_order. apply in_flat_map.
  exists (expr.var w). split; [exact Hein | simpl; auto].
Qed.

(*----per-hypothesis relation/arity facts----*)

(* the per-clause [hsig] shape check, exactly as in [NodeHardwareSemantics.hw_rule_impl]. *)
Abbreviation hsig_ok := (fun (sg : rel_id * nat) (fct : Datalog.fact (_rel := rel_id)) =>
  match fct with
  | nfact R args => R = fst sg /\ length args = snd sg
  | fact.meta _ => False
  end).

(* Each hypothesis fact is the normal fact with the clause's relation and arity, read off
   from [interp_fact]. *)
Lemma interp_hyp_arity (ctx : context) (rule_hyps : list lowered_fact)
    (hyps' : list (Datalog.fact (_rel := rel_id))) (dh : lowered_fact) (i : nat) :
  Forall2 (interp_fact ctx) (rule_hyps) hyps' ->
  i < length rule_hyps ->
  exists tup, nth i hyps' (nfact 0 []) =
                nfact (nth i rule_hyps dh).(Datalog.clause.rel) tup /\
              length tup = length (nth i rule_hyps dh).(Datalog.clause.args).
Proof.
  intros HF Hi. apply Forall2_nth_error_iff in HF. destruct HF as [Hlen Hpt].
  assert (P1 : nth_error (rule_hyps) i = Some ((nth i rule_hyps dh)))
    by (rewrite (nth_error_nth' rule_hyps dh) by lia; reflexivity).
  assert (Hib : i < length hyps') by (rewrite <- Hlen; exact Hi).
  assert (P2 : nth_error hyps' i = Some (nth i hyps' (nfact 0 [])))
    by (apply nth_error_nth'; exact Hib).
  specialize (Hpt i _ _ P1 P2).
  destruct Hpt as [tup [HFa Hyeq]]. exists tup. split.
  - exact Hyeq.
  - apply Forall2_length in HFa. symmetry; exact HFa.
Qed.

(* The [hsig] shape check is exactly what [interp_fact] over the hypotheses provides. *)
Lemma interp_hyps_hsig (ctx : context) (rule_hyps : list lowered_fact)
    (hyps' : list (Datalog.fact (_rel := rel_id))) :
  Forall2 (interp_fact ctx) (rule_hyps) hyps' ->
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) rule_hyps) hyps'.
Proof.
  revert hyps'. induction rule_hyps as [|h lhs IH]; intros hyps' HF.
  - simpl in HF. inversion HF. simpl. constructor.
  - inversion HF as [|x y xs ys Hxy HFrest]; subst.
    rewrite map_cons. constructor.
    + destruct Hxy as [tup [HFa Hyeq]]. subst y. cbn. split; [reflexivity|].
      apply Forall2_length in HFa. symmetry; exact HFa.
    + apply IH; exact HFrest.
Qed.

(* Conversely, the [hsig] shape check yields the per-hypothesis relation/arity facts. *)
Lemma hsig_length (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact (_rel := rel_id))) :
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) rule_hyps) hyps' ->
  length hyps' = length rule_hyps.
Proof.
  intros HF. apply Forall2_length in HF. rewrite length_map in HF. symmetry; exact HF.
Qed.

Lemma hsig_arity (rule_hyps : list lowered_fact) (hyps' : list (Datalog.fact (_rel := rel_id)))
    (dh : lowered_fact) (i : nat) :
  Forall2 hsig_ok
          (map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) rule_hyps) hyps' ->
  i < length rule_hyps ->
  exists tup, nth i hyps' (nfact 0 []) =
                nfact (nth i rule_hyps dh).(Datalog.clause.rel) tup /\
              length tup = length (nth i rule_hyps dh).(Datalog.clause.args).
Proof.
  intros HF Hi. apply Forall2_nth_error_iff in HF. destruct HF as [Hlen Hpt].
  rewrite length_map in Hlen.
  assert (P1 : nth_error (map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) rule_hyps) i
             = Some ((nth i rule_hyps dh).(Datalog.clause.rel), length (nth i rule_hyps dh).(Datalog.clause.args)))
    by (rewrite nth_error_map, (nth_error_nth' rule_hyps dh) by lia; reflexivity).
  assert (Hib : i < length hyps') by (rewrite <- Hlen; exact Hi).
  assert (P2 : nth_error hyps' i = Some (nth i hyps' (nfact 0 [])))
    by (apply nth_error_nth'; exact Hib).
  specialize (Hpt i _ _ P1 P2). cbn in Hpt.
  destruct (nth i hyps' (nfact 0 [])) as [[R tup] | mf]; [|contradiction].
  destruct Hpt as [HR Hl]. exists tup. split.
  - rewrite HR. reflexivity.
  - exact Hl.
Qed.

(* MAIN PER-RULE BRIDGE: a hardware rule whose query, conclusions, and signature are what
   [compile_rule] emits for a bare lowered rule [lr] -- over an ordering [ord] that is exactly
   [lr]'s hypothesis variables, with per-hypothesis tries [tb] registered in [tries] -- derives
   exactly the facts [lr] derives.  This discharges [NodeHardwareSemantics.hw_rule_matches] for compiled
   rules (bare/SuperNice fragment), combining [generate_query_correct] (hypotheses) with
   [concl_exists_iff] (conclusions). *)
Theorem hw_rule_correct
    (concls hyps : list lowered_fact) (hr : hardware_rule)
    (ord : list exprvar) (tb : list trie) (tries : list trie) (dt : trie) (dh : lowered_fact) :
  NoDup ord ->
  Forall bare_fact hyps ->
  Forall bare_fact concls ->
  length tb = length hyps ->
  (forall v, In v (flat_map compute_var_order hyps) -> In v ord) ->
  (forall v, In v ord -> In v (flat_map compute_var_order hyps)) ->
  hr.(hhyps) = generate_query tb ord hyps ->
  hr.(hsig) = map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) hyps ->
  Forall2 (concl_corr ord) concls hr.(hconcls) ->
  (forall i, i < length hyps ->
     (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause.rel) /\
     (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
                               (compute_var_order (nth i hyps dh)) ord /\
     lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt)) ->
  hw_rule_matches tries (Datalog.rule.impl concls hyps) hr.
Proof.
  intros Hnd Hbareh Hbarec Htbl Hcov Hord_sub Hhhyps Hhsig Hconcl Htrie.
  intros nf hyps'. unfold hw_rule_impl. split.
  - (* hardware derivation -> datalog derivation *)
    intros [Hsig [vals [Hqs [jo [Hin Hjo]]]]].
    rewrite Hhsig in Hsig.
    pose proof (hsig_length _ _ Hsig) as Hlenh.
    assert (Hvl : length vals = length ord).
    { destruct Hqs as [Hqlen _]. rewrite Hhhyps, generate_query_length in Hqlen. exact Hqlen. }
    assert (Hstruct : forall i, i < length hyps ->
       (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause.rel) /\
       (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
                                 (compute_var_order (nth i hyps dh)) ord /\
       lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
       exists tup, nth i hyps' (nfact 0 []) =
                     nfact (nth i hyps dh).(Datalog.clause.rel) tup /\
                   length tup = length (nth i hyps dh).(Datalog.clause.args)).
    { intros i Hi. destruct (Htrie i Hi) as [H1 [H2 H3]].
      destruct (hsig_arity hyps hyps' dh i Hsig Hi) as [tup [Hnf Hlt]].
      repeat split; try assumption. exists tup. split; assumption. }
    rewrite Hhhyps in Hqs.
    apply (proj1 (generate_query_correct ord hyps tb tries vals hyps' dt dh
                    Hnd Hbareh Htbl Hlenh Hvl Hcov Hstruct)) in Hqs.
    destruct Hqs as [ctx [Hctx Hfa]].
    apply (proj2 (lrule_impl_iff concls hyps nf hyps')).
    exists ctx. split; [exact Hfa|].
    apply (proj1 (concl_exists_iff ord vals ctx concls hr.(hconcls) nf
                    Hnd (eq_sym Hvl) Hctx Hconcl)).
    apply Exists_exists. exists jo. split; [exact Hin | exact Hjo].
  - (* datalog derivation -> hardware derivation *)
    intros Hri. apply lrule_impl_iff in Hri.
    destruct Hri as [ctx [Hfa Hex]].
    (* the context is defined on every ordering variable (= hypothesis variable) *)
    assert (Hdom : forall v, In v ord -> exists t, map.get ctx v = Some t).
    { intros v Hv. apply Hord_sub in Hv. apply in_flat_map in Hv.
      destruct Hv as [h [Hh Hvco]].
      assert (Hbh : bare_fact h) by (rewrite Forall_forall in Hbareh; auto).
      assert (HLvar : In (expr.var v) h.(Datalog.clause.args)).
      { unfold DistributedDatalogToHardwareCompiler.compute_var_order in Hvco. apply in_flat_map in Hvco.
        destruct Hvco as [arg [Harg Hva]]. unfold bare_fact in Hbh. rewrite Forall_forall in Hbh.
        destruct (Hbh arg Harg) as [w Hw]. subst arg. simpl in Hva.
        destruct Hva as [Heq | []]. subst w. exact Harg. }
      destruct (Forall2_In_l _ _ _ (h) Hfa Hh) as [y [_ Hint]].
      destruct Hint as [tup [HFa Hyeq]].
      destruct (Forall2_In_l _ _ _ (expr.var v) HFa HLvar) as [u [_ Hiu]].
      apply interp_var_iff in Hiu. exists u. exact Hiu. }
    (* build the binding [vals] from the context over the ordering *)
    assert (HforallOrd : Forall (fun v => In v ord) ord)
      by (apply Forall_forall; intros; assumption).
    destruct (map.getmany_of_list_exists ctx (fun v => In v ord) ord HforallOrd Hdom)
      as [vals Hvals].
    pose proof (map.getmany_of_list_length _ _ _ Hvals) as Hlenov.
    destruct (ctx_of_exists ord vals Hlenov) as [ctx' Hctx'].
    assert (Hagree : forall v, In v ord -> map.get ctx' v = map.get ctx v).
    { intros v Hv. destruct (In_nth_error _ _ Hv) as [i Hi].
      assert (Hilt : i < length ord) by (apply nth_error_Some; congruence).
      destruct (nth_error vals i) as [t|] eqn:Evt;
        [|exfalso; apply nth_error_None in Evt; lia].
      rewrite (ctx_get_eq_nth ord vals ctx' i v Hnd Hlenov Hctx' Hi), Evt.
      symmetry. exact (map.getmany_of_list_get ord i ctx vals v t Hvals Hi Evt). }
    (* transport the hypotheses' interpretation to [ctx'] *)
    assert (Hfa' : Forall2 (interp_fact ctx') (hyps) hyps').
    { eapply Forall2_impl_strong; [exact Hfa|].
      intros lf y Hif Hinlf _.
      eapply interp_fact_agree_on; [exact Hif|].
      apply Forall_forall. intros v Hvin. red. symmetry. apply Hagree.
      apply Hcov. apply in_flat_map. exists lf. split; [exact Hinlf|].
      apply bare_vars_in_cvo; [rewrite Forall_forall in Hbareh; auto | exact Hvin]. }
    assert (Hlenh : length hyps' = length hyps).
    { pose proof Hfa as HfaC. apply Forall2_nth_error_iff in HfaC.
      destruct HfaC as [Hl _]. exact (eq_sym Hl). }
    assert (Hstruct : forall i, i < length hyps ->
       (nth i tb dt).(trel) = (nth i hyps dh).(Datalog.clause.rel) /\
       (nth i tb dt).(tperm) = DistributedDatalogToHardwareCompiler.compute_permutation (var_eqb := var_eqb)
                                 (compute_var_order (nth i hyps dh)) ord /\
       lookup_trie tries (nth i tb dt).(tid) = Some (nth i tb dt) /\
       exists tup, nth i hyps' (nfact 0 []) =
                     nfact (nth i hyps dh).(Datalog.clause.rel) tup /\
                   length tup = length (nth i hyps dh).(Datalog.clause.args)).
    { intros i Hi. destruct (Htrie i Hi) as [H1 [H2 H3]].
      destruct (interp_hyp_arity ctx hyps hyps' dh i Hfa Hi) as [tup [Hnf Hlt]].
      repeat split; try assumption. exists tup. split; assumption. }
    split.
    + rewrite Hhsig. apply (interp_hyps_hsig ctx). exact Hfa.
    + exists vals. split.
      * rewrite Hhhyps.
        apply (proj2 (generate_query_correct ord hyps tb tries vals hyps' dt dh
                        Hnd Hbareh Htbl Hlenh (eq_sym Hlenov) Hcov Hstruct)).
        exists ctx'. split; [exact Hctx' | exact Hfa'].
      * assert (Hex' : Exists (fun c => clause.interp ctx' c nf) concls).
        { eapply exists_interp_transport; [exact Hconcl | | exact Hex].
          intros v Hv. symmetry. apply Hagree; exact Hv. }
        apply (proj2 (concl_exists_iff ord vals ctx' concls hr.(hconcls) nf
                        Hnd Hlenov Hctx' Hconcl)) in Hex'.
        apply Exists_exists in Hex'. destruct Hex' as [jo [Hin Hjo]].
        exists jo. split; [exact Hin | exact Hjo].
Qed.

End DistributedDatalogToHardwareCompilerCorrect.

(*============================================================================*)
(*  Discharge lemmas: structural facts about [DistributedDatalogToHardwareCompiler.compile_rule]'s      *)
(*  output that feed [hw_rule_correct].  These are the *definitional* facts      *)
(*  (the per-hypothesis trie's relation/permutation, the query shape, and the    *)
(*  conclusion index correspondence).  They need DistributedDatalogToHardwareCompiler's full parameter   *)
(*  context, hence their own section here -- the compiler file stays proof-free. *)
(*                                                                               *)
(*  The remaining obligations are algorithmic: that                              *)
(*  [compute_variable_ordering_ordered] is NoDup and covers exactly the          *)
(*  hypothesis variables, and that the per-rule tries are registered in the      *)
(*  node's trie table with unique ids (an invariant threaded through             *)
(*  [compile_node]).                                                             *)
(*============================================================================*)

Section CompileDischarge.

Import ResultMonadNotations.
Open Scope result_monad_scope.

(* DistributedDatalogToHardwareCompiler's parameter context (the subset the relevant definitions use). *)
Context {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.
Context {node_id : node_idT}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
#[local] Existing Instance rel_id.
Context {var_idx_map : map.map var nat}.

(* [generate_trie] always returns a trie indexing the hypothesis's relation by the
   permutation computed for that hypothesis -- whether it freshly allocates one or
   reuses an existing trie found by [find] (whose predicate forces both fields). *)
Lemma generate_trie_spec (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing nc = (t, nc') ->
  t.(trel) = hyp.(Datalog.clause.rel) /\
  t.(tperm) = compute_permutation (compute_var_order hyp) ord.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.generate_trie in H. cbv zeta in H.
  destruct (List.find _ existing) as [t0|] eqn:Hfind; inversion H; subst; clear H.
  - apply List.find_some in Hfind. destruct Hfind as [_ Hpred].
    apply andb_true_iff in Hpred. destruct Hpred as [Hrel Hperm].
    destruct (eqb_boolspec _ t.(trel) hyp.(Datalog.clause.rel)) as [Er|Nr];
      [|discriminate Hrel].
    destruct (eqb_boolspec _ t.(tperm) (compute_permutation (compute_var_order hyp) ord)) as [Ep|Np];
      [|discriminate Hperm].
    split; assumption.
  - split; reflexivity.
Qed.

(* The per-hypothesis trie list [compile_hyps] threads (in reverse) matches the
   hypotheses one-for-one with [generate_trie]'s relation/permutation facts. *)
Lemma compile_hyps_fold (ord : list var) (all_rels : list rel_id) (hyps : list lowered_fact) :
  forall (pool0 rev0 : list trie) (nc0 : node_context)
         (pool1 rev1 : list trie) (nc1 : node_context),
  fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp ord pool ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (pool0, rev0, nc0)
    = (pool1, rev1, nc1) ->
  exists ts, rev1 = (List.rev ts ++ rev0)%list /\ List.length ts = List.length hyps /\
    Forall2 (fun t hyp => t.(trel) = hyp.(Datalog.clause.rel) /\
                          t.(tperm) = compute_permutation (compute_var_order hyp) ord) ts hyps.
Proof.
  induction hyps as [|hyp hyps IH]; intros pool0 rev0 nc0 pool1 rev1 nc1 H; simpl in H.
  - inversion H; subst. exists []. simpl. split; [reflexivity|]. split; [reflexivity|constructor].
  - destruct (generate_trie hyp ord pool0 nc0) as [t nc0'] eqn:Hgt.
    destruct (IH (t :: pool0) (t :: rev0) nc0' pool1 rev1 nc1 H) as [ts [Hrev [Hlen HF]]].
    exists (t :: ts). split.
    + simpl. rewrite Hrev. rewrite <- app_assoc. reflexivity.
    + split; [simpl; rewrite Hlen; reflexivity|].
      constructor; [apply (generate_trie_spec hyp ord pool0 nc0 t nc0' Hgt) | exact HF].
Qed.

(*----conclusion index correspondence----*)

(* [get_rule_var_index] locates a variable: the returned index really points at it. *)
Lemma get_rule_var_index_sound (ord : list var) (v : var) (idx : nat) :
  get_rule_var_index ord v = Success idx -> List.nth_error ord idx = Some v.
Proof.
  unfold DistributedDatalogToHardwareCompiler.get_rule_var_index.
  destruct (index_of v ord) as [i|] eqn:Hi; [|discriminate].
  intros H. injection H as <-. apply index_of_Some. exact Hi.
Qed.

(* If each element's producer [g] sends a [Success] result to a fact [P a b], then
   [all_success (map g l)] yields the pointwise [Forall2 P].  ([List.all_success_Success_iff]
   from coqutil supplies the underlying elementwise inversion.) *)
Lemma all_success_map_spec {A B} (g : A -> Result.result B) (P : A -> B -> Prop) :
  forall (l : list A) (out : list B),
  Forall (fun a => forall b, g a = Success b -> P a b) l ->
  List.all_success (List.map g l) = Success out ->
  Forall2 P l out.
Proof.
  intros l out HF Has.
  apply List.all_success_Success_iff, Forall2_map_l in Has.
  eapply Forall2_impl_strong; [exact Has|].
  rewrite Forall_forall in HF.
  intros a b Hga Hin _. exact (HF a Hin b Hga).
Qed.

(* A compiled (bare) conclusion's join_output relation and indices correspond to the
   lowered conclusion: each output index is the ordering position of that variable.
   This is exactly [DistributedDatalogToHardwareCompilerCorrect.concl_corr]. *)
Lemma compile_concl_corr (concl : lowered_fact) (all_rels : list rel_id) (ord : list var)
    (jo : join_output) :
  Forall (fun e => exists v, e = expr.var v) concl.(Datalog.clause.args) ->
  compile_concl concl ord = Success jo ->
  jo.(output_rel) = concl.(Datalog.clause.rel) /\
  Forall2 (fun e idx => exists v, e = expr.var v /\ List.nth_error ord idx = Some v)
          concl.(Datalog.clause.args) jo.(output_var_indices).
Proof.
  intros Hbare H. unfold DistributedDatalogToHardwareCompiler.compile_concl in H.
  match type of H with
  | context [List.all_success ?x] => destruct (List.all_success x) as [var_indices|e] eqn:Has
  end; cbn beta iota in H; [|discriminate].
  injection H as <-. cbn. split; [reflexivity|].
  eapply all_success_map_spec; [| exact Has].
  eapply Forall_impl; [exact Hbare |].
  intros a [v ->] b Hb. cbn in Hb.
  exists v; split; [reflexivity | apply get_rule_var_index_sound; exact Hb].
Qed.

(* [compile_concls] yields the per-conclusion correspondence [concl_corr] over the whole list. *)
Lemma compile_concls_corr (concls : list lowered_fact) (all_rels : list rel_id) (ord : list var)
    (jos : list join_output) :
  Forall (fun c => Forall (fun e => exists v, e = expr.var v) c.(Datalog.clause.args)) concls ->
  compile_concls concls ord = Success jos ->
  Forall2 (concl_corr ord) concls jos.
Proof.
  intros Hb H. unfold DistributedDatalogToHardwareCompiler.compile_concls in H.
  eapply all_success_map_spec; [| exact H].
  eapply Forall_impl; [exact Hb |].
  intros c Hc jo Hcc. cbn beta in Hcc.
  exact (compile_concl_corr c all_rels ord jo Hc Hcc).
Qed.

(*----trie registration: each per-rule trie is found in the node's trie table----*)

(* With unique trie ids, [find]-by-id returns exactly the trie. *)
Lemma find_tid_unique (l : list trie) (t : trie) :
  In t l -> NoDup (map (fun x => x.(tid)) l) ->
  find (fun x => Nat.eqb x.(tid) t.(tid)) l = Some t.
Proof.
  induction l as [|x l IH]; intros Hin Hnd; simpl in *; [contradiction|].
  inversion Hnd as [|y ys Hynin Hnd' Heq]; subst.
  destruct (Nat.eqb_spec x.(tid) t.(tid)) as [He|Hne].
  - destruct Hin as [Heq | Hin]; [rewrite Heq; reflexivity|].
    exfalso. apply Hynin. rewrite He. apply in_map; exact Hin.
  - destruct Hin as [-> | Hin]; [congruence | apply IH; assumption].
Qed.

Lemma lookup_trie_some (l : list trie) (t : trie) :
  In t l -> NoDup (map (fun x => x.(tid)) l) ->
  NodeHardwareSemantics.lookup_trie l t.(tid) = Some t.
Proof. unfold NodeHardwareSemantics.lookup_trie. apply find_tid_unique. Qed.

(* Node-context well-formedness: ids are bounded by the fresh-id counter and duplicate-free. *)
Definition wf_nc (nc : node_context) : Prop :=
  (forall t, In t nc.(nctries) -> t.(tid) < nc.(last_trie_id)) /\
  NoDup (map (fun t => t.(tid)) nc.(nctries)).

(* [generate_trie] either reuses an existing trie (context unchanged) or allocates a fresh one. *)
Lemma generate_trie_nctries (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (all_rels : list rel_id) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing nc = (t, nc') ->
  (nc' = nc /\ In t existing) \/
  (nc'.(nctries) = t :: nc.(nctries) /\ nc'.(last_trie_id) = S nc.(last_trie_id) /\
   t.(tid) = nc.(last_trie_id)).
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.generate_trie in H. cbv zeta in H.
  destruct (List.find _ existing) as [t0|] eqn:Hfind; injection H as <- <-.
  - left. apply List.find_some in Hfind. destruct Hfind as [Hin _]. split; [reflexivity | exact Hin].
  - right. split; [reflexivity | split; reflexivity].
Qed.

Lemma generate_trie_wf (hyp : lowered_fact) (ord : list var)
    (existing : list trie) (all_rels : list rel_id) (nc : node_context) (t : trie) (nc' : node_context) :
  generate_trie hyp ord existing nc = (t, nc') ->
  wf_nc nc -> incl existing nc.(nctries) ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\ In t nc'.(nctries).
Proof.
  intros H [Hlt Hnd] Hincl.
  destruct (generate_trie_nctries hyp ord existing all_rels nc t nc' H)
    as [[-> Hin] | [Hnct [Hlast Htid]]].
  - split; [split; assumption | split; [apply incl_refl | apply Hincl; exact Hin]].
  - assert (Hwf : wf_nc nc').
    { split.
      - intros s Hs. rewrite Hnct in Hs. rewrite Hlast.
        destruct Hs as [<- | Hs]; [rewrite Htid; lia | specialize (Hlt s Hs); lia].
      - rewrite Hnct. simpl. constructor; [|exact Hnd].
        rewrite in_map_iff. intros [s [Hseq Hsin]].
        specialize (Hlt s Hsin). rewrite Htid in Hseq. lia. }
    split; [exact Hwf | split].
    + intros s Hs. rewrite Hnct. right. exact Hs.
    + rewrite Hnct. left. reflexivity.
Qed.

(* The [compile_hyps] fold preserves [wf_nc], grows [nctries] monotonically, and keeps every
   chosen per-hypothesis trie inside [nctries] (the pool stays a subset of the node's tries). *)
Lemma compile_hyps_fold_reg (ord : list var) (all_rels : list rel_id) (hyps : list lowered_fact) :
  forall (pool0 rev0 : list trie) (nc0 : node_context)
         (pool1 rev1 : list trie) (nc1 : node_context),
  fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp ord pool ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (pool0, rev0, nc0) = (pool1, rev1, nc1) ->
  wf_nc nc0 -> incl pool0 nc0.(nctries) -> (forall t, In t rev0 -> In t nc0.(nctries)) ->
  wf_nc nc1 /\ incl nc0.(nctries) nc1.(nctries) /\ incl pool1 nc1.(nctries) /\
  (forall t, In t rev1 -> In t nc1.(nctries)).
Proof.
  induction hyps as [|hyp hyps IH];
    intros pool0 rev0 nc0 pool1 rev1 nc1 H Hwf Hpool Hrev; simpl in H.
  - inversion H; subst.
    split; [exact Hwf | split; [apply incl_refl | split; [exact Hpool | exact Hrev]]].
  - destruct (generate_trie hyp ord pool0 nc0) as [t nc0'] eqn:Hgt.
    destruct (generate_trie_wf hyp ord pool0 all_rels nc0 t nc0' Hgt Hwf Hpool) as [Hwf' [Hmono Htin]].
    assert (Hpool' : incl (t :: pool0) nc0'.(nctries))
      by (apply incl_cons; [exact Htin | intros s Hs; apply Hmono; apply Hpool; exact Hs]).
    assert (Hrev' : forall s, In s (t :: rev0) -> In s nc0'.(nctries))
      by (intros s [<- | Hs]; [exact Htin | apply Hmono; apply Hrev; exact Hs]).
    destruct (IH (t :: pool0) (t :: rev0) nc0' pool1 rev1 nc1 H Hwf' Hpool' Hrev')
      as [Hwf1 [Hmono1 [Hpool1 Hrev1]]].
    split; [exact Hwf1 |
            split; [apply (incl_tran Hmono Hmono1) | split; [exact Hpool1 | exact Hrev1]]].
Qed.

(* Top-level: [compile_hyps] (started from the node's own tries) preserves [wf_nc], grows the
   trie table, and yields the per-hypothesis trie list -- all of whose tries are registered. *)
Lemma compile_hyps_reg (hyps : list lowered_fact) (ord : list var) (all_rels : list rel_id)
    (nc : node_context) (q : query) (nc' : node_context) :
  compile_hyps hyps ord nc.(nctries) nc = (q, nc') ->
  wf_nc nc ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\
  (exists tb, q = generate_query tb ord hyps /\ (forall t, In t tb -> In t nc'.(nctries))).
Proof.
  intros H Hwf. unfold DistributedDatalogToHardwareCompiler.compile_hyps in H.
  match type of H with
  | context [fold_left ?F hyps ?init] =>
      destruct (fold_left F hyps init) as [[pool1 rev1] nc1] eqn:Hfold
  end.
  cbn beta iota zeta in H. injection H as Hq Hnc; subst q nc'.
  assert (Hrev0 : forall t, In t (@nil trie) -> In t nc.(nctries)) by (intros t []).
  destruct (compile_hyps_fold_reg ord all_rels hyps nc.(nctries) [] nc pool1 rev1 nc1
              Hfold Hwf (incl_refl _) Hrev0) as [Hwf1 [Hmono [_ Hrevin]]].
  split; [exact Hwf1 | split; [exact Hmono |]].
  exists (rev rev1). split; [reflexivity|].
  intros t Htb. apply Hrevin. rewrite in_rev. exact Htb.
Qed.

(* Combined: one [tb] with both the relation/permutation facts and the registration. *)
Lemma compile_hyps_full (hyps : list lowered_fact) (ord : list var) (all_rels : list rel_id)
    (nc : node_context) (q : query) (nc' : node_context) :
  compile_hyps hyps ord nc.(nctries) nc = (q, nc') ->
  wf_nc nc ->
  wf_nc nc' /\ incl nc.(nctries) nc'.(nctries) /\
  exists tb, q = generate_query tb ord hyps /\ List.length tb = List.length hyps /\
    Forall2 (fun t hyp => t.(trel) = hyp.(Datalog.clause.rel) /\
                          t.(tperm) = compute_permutation (compute_var_order hyp) ord) tb hyps /\
    (forall t, In t tb -> In t nc'.(nctries)).
Proof.
  intros H Hwf. unfold DistributedDatalogToHardwareCompiler.compile_hyps in H.
  match type of H with
  | context [fold_left ?F hyps ?init] =>
      destruct (fold_left F hyps init) as [[pool1 rev1] nc1] eqn:Hfold
  end.
  cbn beta iota zeta in H. injection H as Hq Hnc; subst nc'.
  destruct (compile_hyps_fold ord all_rels hyps nc.(nctries) [] nc pool1 rev1 nc1 Hfold)
    as [ts [Hrev [Hlen HFtt]]].
  assert (Hrev0 : forall t, In t (@nil trie) -> In t nc.(nctries)) by (intros t []).
  destruct (compile_hyps_fold_reg ord all_rels hyps nc.(nctries) [] nc pool1 rev1 nc1
              Hfold Hwf (incl_refl _) Hrev0) as [Hwf1 [Hmono [_ Hrevin]]].
  split; [exact Hwf1 | split; [exact Hmono |]].
  exists ts. split; [|split; [exact Hlen | split; [exact HFtt|]]].
  - rewrite <- Hq, Hrev, app_nil_r, rev_involutive. reflexivity.
  - intros t Ht. apply Hrevin. rewrite Hrev, app_nil_r. rewrite <- in_rev. exact Ht.
Qed.

End CompileDischarge.

(*============================================================================*)
(*  Variable-ordering correctness: [compute_variable_ordering_ordered] over     *)
(*  [create_dependency_graph hyps] returns a duplicate-free list that is         *)
(*  exactly the set of hypothesis variables (the candidates).  This discharges   *)
(*  [hw_rule_correct]'s [NoDup ord], coverage, and subset hypotheses.            *)
(*============================================================================*)

Section OrderingCorrect.

Context {var : exprvarT} {fn : fnT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context {var_node_set : map.map var unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_graph_impl : graph.graph var} {var_graph_impl_ok : graph.ok var_graph_impl}.

Abbreviation ordering_context := (@DistributedDatalogToHardwareCompiler.ordering_context var var_node_set var_graph_impl).
Abbreviation var_graph := (@ComputableGraph var var_node_set var_graph_impl).
Abbreviation choose := (@DistributedDatalogToHardwareCompiler.choose_next_var_ordered var var_node_set var_graph_impl).

(* The generic per-candidate step shared by both max-degree folds: a candidate
   is considered only if it is still a graph node. *)
Definition mstep (ns : var_node_set) (degf : var -> nat)
    (acc : option (var * nat)) (x : var) : option (var * nat) :=
  match map.get ns x with
  | None => acc
  | Some _ =>
    match acc with
    | None => Some (x, degf x)
    | Some (_, md) => if Nat.ltb md (degf x) then Some (x, degf x) else acc
    end
  end.

(* The max-degree fold only ever returns a candidate that is a current graph node. *)
Lemma fold_mstep_acc (ns : var_node_set) (degf : var -> nat) (cs : list var) :
  forall acc0 v d,
  fold_left (mstep ns degf) cs acc0 = Some (v, d) ->
  (In v cs /\ map.get ns v <> None) \/ acc0 = Some (v, d).
Proof.
  induction cs as [|x cs IH]; intros acc0 v d H; simpl in H.
  - right. exact H.
  - apply IH in H. destruct H as [[Hin Hne] | Hacc].
    + left. split; [right; exact Hin | exact Hne].
    + unfold mstep in Hacc. destruct (map.get ns x) as [u|] eqn:Hx.
      * destruct acc0 as [[x0 md]|].
        -- destruct (Nat.ltb md (degf x)).
           ++ injection Hacc as <- <-. left. split; [left; reflexivity | rewrite Hx; discriminate].
           ++ right. exact Hacc.
        -- injection Hacc as <- <-. left. split; [left; reflexivity | rewrite Hx; discriminate].
      * right. exact Hacc.
Qed.

(* And it returns [None] only when no candidate is a current graph node. *)
Lemma fold_mstep_None (ns : var_node_set) (degf : var -> nat) (cs : list var) :
  forall acc0,
  fold_left (mstep ns degf) cs acc0 = None ->
  acc0 = None /\ (forall x, In x cs -> map.get ns x = None).
Proof.
  induction cs as [|x cs IH]; intros acc0 H; simpl in H.
  - split; [exact H | intros x []].
  - apply IH in H. destruct H as [Hstep Hrest].
    unfold mstep in Hstep. destruct (map.get ns x) as [u|] eqn:Hx.
    + destruct acc0 as [[x0 md]|]; [destruct (Nat.ltb md (degf x)); discriminate | discriminate].
    + split; [exact Hstep|]. intros y [<- | Hy]; [exact Hx | apply Hrest; exact Hy].
Qed.

(* [choose] picks a candidate that is a current graph node, ... *)
Lemma choose_Some (ctx : ordering_context) (cs : list var) (v : var) :
  choose ctx cs = Some v ->
  In v cs /\ map.get ctx.(dep_graph).(nodes) v <> None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.choose_next_var_ordered.
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1.
  - intros H. injection H as <-.
    unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered in H1.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (DistributedDatalogToHardwareCompiler.compute_degree_to_visited_set ctx.(dep_graph) ctx.(visited)) cs None v1 d1)
      in H1.
    destruct H1 as [[Hin Hne]|H1]; [split; assumption | discriminate].
  - destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [|discriminate].
    intros H. injection H as <-.
    unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered in H2.
    apply (fold_mstep_acc ctx.(dep_graph).(nodes)
             (DistributedDatalogToHardwareCompiler.compute_degree ctx.(dep_graph)) cs None v2 d2) in H2.
    destruct H2 as [[Hin Hne]|H2]; [split; assumption | discriminate].
Qed.

(* ... and returns [None] only when no candidate is a current graph node. *)
Lemma choose_None (ctx : ordering_context) (cs : list var) :
  choose ctx cs = None ->
  forall v, In v cs -> map.get ctx.(dep_graph).(nodes) v = None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.choose_next_var_ordered.
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_to_visited_set_ordered _ _ _)
    as [[v1 d1]|] eqn:H1; [discriminate|].
  destruct (DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered _ _) as [[v2 d2]|] eqn:H2; [discriminate|].
  intros _ v Hv.
  unfold DistributedDatalogToHardwareCompiler.compute_max_degree_var_ordered in H2.
  apply (fold_mstep_None ctx.(dep_graph).(nodes) (DistributedDatalogToHardwareCompiler.compute_degree ctx.(dep_graph)) cs None)
    in H2.
  destruct H2 as [_ H2]. apply H2; exact Hv.
Qed.

(*----bare hypotheses: collected vars coincide with the variable ordering's vars----*)

Lemma bare_collect_vars_fact (h : lowered_fact) :
  Forall (fun e => exists v, e = expr.var v) h.(Datalog.clause.args) ->
  Datalog.clause.vars h = compute_var_order h.
Proof.
  unfold Datalog.clause.vars, DistributedDatalogToHardwareCompiler.compute_var_order.
  induction h.(Datalog.clause.args) as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [v ->] Hb']; subst. simpl. f_equal. apply IH; exact Hb'.
Qed.

Lemma bare_collect_vars_hyps (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists v, e = expr.var v) h.(Datalog.clause.args)) hyps ->
  flat_map Datalog.clause.vars hyps = flat_map compute_var_order hyps.
Proof.
  induction hyps as [|h hyps IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l Hbh Hb']; subst.
  rewrite (bare_collect_vars_fact h Hbh), (IH Hb'). reflexivity.
Qed.

(*----the greedy loop: NoDup + subset + full coverage----*)

Abbreviation cvo_h := (@DistributedDatalogToHardwareCompiler.compute_variable_ordering_ordered_h var var_node_set var_graph_impl).

(* [innode]/[node_count]: how many candidates are still graph nodes (the loop's measure). *)
Definition innode (ns : var_node_set) (v : var) : bool :=
  match map.get ns v with Some _ => true | None => false end.
Definition node_count (ns : var_node_set) (cs : list var) : nat :=
  length (filter (innode ns) cs).

Lemma cvo_h_S (ctx : ordering_context) (cs : list var) (fuel : nat) :
  cvo_h ctx cs (S fuel)
  = match choose ctx cs with Some v => cvo_h (visit_node v ctx) cs fuel | None => ctx end.
Proof. reflexivity. Qed.

Lemma visit_order (v : var) (ctx : ordering_context) :
  (visit_node v ctx).(order) = v :: ctx.(order).
Proof. reflexivity. Qed.
Lemma visit_nodes (v : var) (ctx : ordering_context) :
  (visit_node v ctx).(dep_graph).(nodes) = map.remove ctx.(dep_graph).(nodes) v.
Proof. reflexivity. Qed.

(* Two filters that disagree only at one (present, NoDup) element differ in count by one. *)
Lemma filter_diff_one (f g : var -> bool) (cs : list var) (v : var) :
  NoDup cs -> In v cs -> f v = true -> g v = false ->
  (forall w, w <> v -> g w = f w) ->
  length (filter g cs) = pred (length (filter f cs)).
Proof.
  intros Hnd Hin Hfv Hgv Hdiff.
  induction cs as [|x cs IH]; simpl in Hin; [contradiction|].
  inversion Hnd as [|x0 cs0 Hxnin Hnd' Heq]; subst.
  simpl. destruct Hin as [<- | Hin].
  - rewrite Hfv, Hgv. simpl.
    rewrite (filter_ext_in g f cs); [reflexivity|].
    intros w Hw. apply Hdiff. intros ->. apply Hxnin; exact Hw.
  - rewrite (Hdiff x ltac:(intros ->; apply Hxnin; exact Hin)).
    destruct (f x) eqn:Hfx; simpl.
    + rewrite (IH Hnd' Hin).
      assert (Hge : 1 <= length (filter f cs)).
      { destruct (filter f cs) eqn:Ef; [|simpl; lia].
        assert (Hvf : In v (filter f cs)) by (apply filter_In; split; assumption).
        rewrite Ef in Hvf. destruct Hvf. }
      lia.
    + apply (IH Hnd' Hin).
Qed.

Lemma node_count_remove (ns : var_node_set) (cs : list var) (v : var) :
  NoDup cs -> In v cs -> map.get ns v <> None ->
  node_count (map.remove ns v) cs = pred (node_count ns cs).
Proof.
  intros Hnd Hin Hne. unfold node_count.
  apply (filter_diff_one (innode ns) (innode (map.remove ns v)) cs v Hnd Hin).
  - unfold innode. destruct (map.get ns v); [reflexivity | exfalso; apply Hne; reflexivity].
  - unfold innode. rewrite map.get_remove_same. reflexivity.
  - intros w Hwv. unfold innode. rewrite (map.get_remove_diff ns w v Hwv). reflexivity.
Qed.

Lemma node_count_zero (ns : var_node_set) (cs : list var) :
  node_count ns cs = 0 -> forall v, In v cs -> map.get ns v = None.
Proof.
  unfold node_count. intros H v Hv.
  destruct (map.get ns v) as [u|] eqn:Hg; [|reflexivity].
  exfalso. assert (Hvf : In v (filter (innode ns) cs)).
  { apply filter_In. split; [exact Hv | unfold innode; rewrite Hg; reflexivity]. }
  destruct (filter (innode ns) cs); [destruct Hvf | simpl in H; discriminate].
Qed.

(* The loop, run with enough fuel, produces a duplicate-free ordering whose elements are
   exactly the candidates: NoDup, [order ⊆ cs], and [cs ⊆ order]. *)
Lemma cvo_h_spec (cs : list var) (Hcs : NoDup cs) :
  forall (fuel : nat) (ctx : ordering_context),
  NoDup ctx.(order) ->
  (forall w, In w ctx.(order) -> In w cs) ->
  (forall w, In w ctx.(order) -> map.get ctx.(dep_graph).(nodes) w = None) ->
  (forall w, In w cs -> In w ctx.(order) \/ map.get ctx.(dep_graph).(nodes) w <> None) ->
  node_count ctx.(dep_graph).(nodes) cs <= fuel ->
  NoDup (cvo_h ctx cs fuel).(order) /\
  (forall w, In w (cvo_h ctx cs fuel).(order) -> In w cs) /\
  (forall w, In w cs -> In w (cvo_h ctx cs fuel).(order)).
Proof.
  intros fuel. induction fuel as [|fuel IH]; intros ctx Hnd Hsub Hrm Hk Hcount.
  - assert (Hz : node_count ctx.(dep_graph).(nodes) cs = 0) by lia.
    split; [exact Hnd | split; [exact Hsub|]].
    intros w Hw. destruct (Hk w Hw) as [Ho | Hne]; [exact Ho|].
    exfalso. apply Hne. apply (node_count_zero _ _ Hz w Hw).
  - rewrite cvo_h_S. destruct (choose ctx cs) as [v|] eqn:Hchoose.
    + destruct (choose_Some ctx cs v Hchoose) as [Hvcs Hvne].
      assert (Hvno : ~ In v ctx.(order)) by (intros Hvo; apply Hvne; apply Hrm; exact Hvo).
      apply IH.
      * rewrite visit_order. constructor; [exact Hvno | exact Hnd].
      * intros w. rewrite visit_order. intros [<- | Hw]; [exact Hvcs | apply Hsub; exact Hw].
      * intros w. rewrite visit_order, visit_nodes. intros [<- | Hw].
        -- rewrite map.get_remove_same. reflexivity.
        -- assert (Hwv : w <> v) by (intros ->; apply Hvno; exact Hw).
           rewrite (map.get_remove_diff _ w v Hwv). apply Hrm; exact Hw.
      * intros w Hw. rewrite visit_order, visit_nodes.
        destruct (Hk w Hw) as [Ho | Hne].
        -- left; right; exact Ho.
        -- destruct (Eqb_ok_BoolSpec w v) as [->|Hwv].
           ++ left; left; reflexivity.
           ++ right. rewrite (map.get_remove_diff _ w v Hwv). exact Hne.
      * rewrite visit_nodes.
        rewrite (node_count_remove ctx.(dep_graph).(nodes) cs v Hcs Hvcs Hvne). lia.
    + split; [exact Hnd | split; [exact Hsub|]].
      intros w Hw. destruct (Hk w Hw) as [Ho | Hne]; [exact Ho|].
      exfalso. apply Hne. apply (choose_None ctx cs Hchoose w Hw).
Qed.

(*----every collected variable is a node of the dependency graph (bare fragment)----*)

(* The reverse-edge [map.fold] inside [add_arg_edges] leaves the node set unchanged. *)
Lemma addarg_fold_nodes (F : var_graph -> var -> unit -> var_graph)
    (g0 : var_graph) (cv : var_node_set) :
  (forall acc u x, (F acc u x).(nodes) = acc.(nodes)) ->
  (map.fold F g0 cv).(nodes) = g0.(nodes).
Proof.
  intros HF.
  apply (map.fold_spec (fun (_ : var_node_set) (g : var_graph) => g.(nodes) = g0.(nodes)) F g0).
  - reflexivity.
  - intros k val m r _ Hr. rewrite HF. exact Hr.
Qed.

(* So adding a bare argument [expr.var v] puts exactly [v] into the node set. *)
Lemma add_arg_edges_LVar_nodes (v : var) (g : var_graph) (cv : var_node_set) :
  (DistributedDatalogToHardwareCompiler.add_arg_edges (expr.var v) g cv).(nodes) = map.put g.(nodes) v tt.
Proof.
  cbn [DistributedDatalogToHardwareCompiler.add_arg_edges].
  erewrite addarg_fold_nodes; [reflexivity | intros acc u x; reflexivity].
Qed.

Lemma add_args_edges_mono (args : list (@HardwareProgram.lowered_expr var fn)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = expr.var u) args ->
  map.get g.(nodes) w <> None ->
  map.get (DistributedDatalogToHardwareCompiler.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hg; simpl; [exact Hg|].
  inversion Hb as [|x l [u ->] Hb']; subst.
  apply (IH (DistributedDatalogToHardwareCompiler.add_arg_edges (expr.var u) g seen) (map.put seen u tt) w Hb').
  rewrite add_arg_edges_LVar_nodes.
  destruct (Eqb_ok_BoolSpec u w) as [->|Hne].
  - rewrite map.get_put_same. discriminate.
  - rewrite (map.get_put_diff g.(nodes) w tt u (not_eq_sym Hne)). exact Hg.
Qed.

Lemma add_args_edges_covers (args : list (@HardwareProgram.lowered_expr var fn)) :
  forall (g : var_graph) (seen : var_node_set) (w : var),
  Forall (fun e => exists u, e = expr.var u) args ->
  In (expr.var w) args ->
  map.get (DistributedDatalogToHardwareCompiler.add_args_edges args g seen).(nodes) w <> None.
Proof.
  induction args as [|a args IH]; intros g seen w Hb Hin; simpl in Hin; [contradiction|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. destruct Hin as [Heq | Hin].
  - injection Heq as ->.
    apply (add_args_edges_mono args (DistributedDatalogToHardwareCompiler.add_arg_edges (expr.var w) g seen)
             (map.put seen w tt) w Hb').
    rewrite add_arg_edges_LVar_nodes, map.get_put_same. discriminate.
  - apply (IH (DistributedDatalogToHardwareCompiler.add_arg_edges (expr.var u) g seen) (map.put seen u tt) w Hb' Hin).
Qed.

(* Bare: a fact's collected variables are exactly its [expr.var] arguments. *)
Lemma bare_in_collect_args (args : list (@HardwareProgram.lowered_expr var fn)) (w : var) :
  Forall (fun e => exists u, e = expr.var u) args ->
  (In w (flat_map Datalog.expr.vars args) <-> In (expr.var w) args).
Proof.
  induction args as [|a args IH]; intros Hb; simpl; [reflexivity|].
  inversion Hb as [|x l [u ->] Hb']; subst. simpl. rewrite (IH Hb'). split.
  - intros [<- | Hin]; [left; reflexivity | right; exact Hin].
  - intros [Heq | Hin]; [injection Heq as ->; left; reflexivity | right; exact Hin].
Qed.

Lemma add_hyp_edges_mono (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = expr.var u) h.(Datalog.clause.args) ->
  map.get g.(nodes) w <> None ->
  map.get (DistributedDatalogToHardwareCompiler.add_hyp_edges h g).(nodes) w <> None.
Proof. unfold DistributedDatalogToHardwareCompiler.add_hyp_edges. intros. apply add_args_edges_mono; assumption. Qed.

Lemma add_hyp_edges_covers (h : lowered_fact) (g : var_graph) (w : var) :
  Forall (fun e => exists u, e = expr.var u) h.(Datalog.clause.args) ->
  In w (Datalog.clause.vars h) ->
  map.get (DistributedDatalogToHardwareCompiler.add_hyp_edges h g).(nodes) w <> None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.add_hyp_edges, Datalog.clause.vars. intros Hb Hin.
  apply add_args_edges_covers; [exact Hb | apply (bare_in_collect_args h.(Datalog.clause.args) w Hb); exact Hin].
Qed.

(* The whole dependency graph: every collected hypothesis variable is a node. *)
Lemma create_dep_graph_covers (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists u, e = expr.var u) h.(Datalog.clause.args)) hyps ->
  forall w, In w (flat_map Datalog.clause.vars hyps) ->
  map.get (DistributedDatalogToHardwareCompiler.create_dependency_graph hyps).(nodes) w <> None.
Proof.
  unfold DistributedDatalogToHardwareCompiler.create_dependency_graph.
  (* generalize the initial accumulator graph *)
  assert (Hgen : forall (hs : list lowered_fact) (g : var_graph) w,
            Forall (fun h => Forall (fun e => exists u, e = expr.var u) h.(Datalog.clause.args)) hs ->
            (In w (flat_map Datalog.clause.vars hs) \/ map.get g.(nodes) w <> None) ->
            map.get (fold_left (fun acc h => DistributedDatalogToHardwareCompiler.add_hyp_edges h acc) hs g).(nodes) w
              <> None).
  { intros hs. induction hs as [|h hs IH]; intros g w Hb Hor; simpl.
    - destruct Hor as [[] | Hg]; exact Hg.
    - inversion Hb as [|x l Hbh Hb']; subst.
      apply IH; [exact Hb'|].
      simpl in Hor. destruct Hor as [Hin | Hg].
      + apply in_app_or in Hin. destruct Hin as [Hh | Hrest].
        * right. apply add_hyp_edges_covers; [exact Hbh | exact Hh].
        * left. exact Hrest.
      + right. apply add_hyp_edges_mono; [exact Hbh | exact Hg]. }
  intros Hb w Hin. apply (Hgen hyps DistributedDatalogToHardwareCompiler.empty_ComputableGraph w Hb). left. exact Hin.
Qed.

(*----assembly: the produced ordering is NoDup and exactly the hypothesis variables----*)

Lemma length_filter_le {A} (f : A -> bool) (l : list A) : length (filter f l) <= length l.
Proof. induction l as [|x l IH]; simpl; [lia | destruct (f x); simpl; lia]. Qed.

(* MAIN ordering correctness: for bare hypotheses, the variable ordering computed over the
   dependency graph is duplicate-free and contains exactly the hypothesis variables.  This
   discharges [hw_rule_correct]'s [NoDup ord], coverage, and subset hypotheses. *)
Lemma compute_variable_ordering_ordered_correct (hyps : list lowered_fact) :
  Forall (fun h => Forall (fun e => exists u, e = expr.var u) h.(Datalog.clause.args)) hyps ->
  NoDup (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps) /\
  (forall v, In v (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps) ->
             In v (flat_map compute_var_order hyps)) /\
  (forall v, In v (flat_map compute_var_order hyps) ->
             In v (compute_variable_ordering_ordered (create_dependency_graph hyps) hyps)).
Proof.
  intros Hb.
  assert (Hcv : flat_map Datalog.clause.vars hyps = flat_map compute_var_order hyps)
    by (apply bare_collect_vars_hyps; exact Hb).
  unfold DistributedDatalogToHardwareCompiler.compute_variable_ordering_ordered. cbv zeta.
  set (g := create_dependency_graph hyps).
  set (cs := DistributedDatalogToHardwareCompiler.hyp_var_order hyps).
  assert (HcandIn : forall v, In v cs <-> In v (flat_map Datalog.clause.vars hyps)).
  { intros v. unfold cs, DistributedDatalogToHardwareCompiler.hyp_var_order.
    symmetry. apply dedup_preserves_In. }
  assert (Hcs : NoDup cs) by (unfold cs, DistributedDatalogToHardwareCompiler.hyp_var_order; apply NoDup_dedup).
  assert (HP1 : NoDup (initial_ordering_context g).(order)) by (simpl; constructor).
  assert (HP2 : forall w, In w (initial_ordering_context g).(order) -> In w cs)
    by (simpl; intros w []).
  assert (HP3 : forall w, In w (initial_ordering_context g).(order) ->
                  map.get (initial_ordering_context g).(dep_graph).(nodes) w = None)
    by (simpl; intros w []).
  assert (HP4 : forall w, In w cs -> In w (initial_ordering_context g).(order) \/
                  map.get (initial_ordering_context g).(dep_graph).(nodes) w <> None).
  { intros w Hw. right. simpl.
    apply create_dep_graph_covers; [exact Hb | exact (proj1 (HcandIn w) Hw)]. }
  assert (HP5 : node_count (initial_ordering_context g).(dep_graph).(nodes) cs <= length cs)
    by (unfold node_count; apply length_filter_le).
  destruct (cvo_h_spec cs Hcs (length cs) (initial_ordering_context g) HP1 HP2 HP3 HP4 HP5)
    as [Hnd [Hsub Hcov]].
  split; [| split].
  - apply NoDup_rev. exact Hnd.
  - intros v Hv. rewrite <- in_rev in Hv. rewrite <- Hcv.
    exact (proj1 (HcandIn v) (Hsub v Hv)).
  - intros v Hv. rewrite <- in_rev. apply Hcov, (proj2 (HcandIn v)). rewrite <- Hcv in Hv. exact Hv.
Qed.

End OrderingCorrect.

(*============================================================================*)
(*  Trie registration at the node level: [compile_node]'s trie table has        *)
(*  duplicate-free ids (so [lookup_trie] finds each registered trie), and the    *)
(*  table grows monotonically across rules.                                      *)
(*============================================================================*)

Section RegisterNode.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context {var : exprvarT} {fn : fnT} {aggregator : aggregatorT}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.
Context {fn_eqb : Eqb fn} {fn_eqb_ok : Eqb_ok fn_eqb}.
Context {node_id : node_idT}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map (rel_id * fwd_from) (list fwd_to)}.
#[local] Existing Instance rel_id.
Context {var_node_set : map.map var unit}.
Context {var_graph_impl : graph.graph var} {var_graph_impl_ok : graph.ok var_graph_impl}.
Context {var_idx_map : map.map var nat}.

(* [compile_rule] = [compile_hyps] (which threads the trie context) then [compile_concls]
   (which leaves the context untouched), so it preserves [wf_nc] and grows [nctries]. *)
Lemma compile_rule_reg (rule : lowered_rule) (all_rels : list rel_id) (nc : node_context)
    (hr : hardware_rule) (nc' : node_context) :
  compile_rule rule nc = Success (hr, nc') ->
  wf_nc nc -> wf_nc nc' /\ incl nc.(nctries) nc'.(nctries).
Proof.
  unfold DistributedDatalogToHardwareCompiler.compile_rule. intros H Hwf.
  destruct rule as [rconcls rhyps | cr ag hyp_rel];
    cbv zeta in H; [| discriminate].
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_hyps ?a ?b ?c ?d] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_hyps a b c d) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_concls ?a ?b] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_concls a b) as [concls|] eqn:Hcc
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as _ <-.
  destruct (compile_hyps_reg rhyps _ all_rels nc q nc'' Hch Hwf) as [Hwf'' [Hmono _]].
  split; assumption.
Qed.

(* Errored accumulator stays errored across the [compile_node] fold. *)
Lemma compile_node_fold_error (prog : lowered_program) :
  forall (e : dlist.dlist),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Failure e) = Failure e.
Proof. induction prog as [|r prog IH]; intros e; simpl; [reflexivity | apply IH]. Qed.

(* The [compile_node] fold preserves [wf_nc] and grows [nctries]. *)
Lemma compile_node_fold_wf (all_rels : list rel_id) (prog : lowered_program) :
  forall (rules0 : list hardware_rule) (nc0 : node_context)
         (res : list hardware_rule) (nc1 : node_context),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Success (rules0, nc0)) = Success (res, nc1) ->
  wf_nc nc0 -> wf_nc nc1 /\ incl nc0.(nctries) nc1.(nctries).
Proof.
  induction prog as [|r prog IH]; intros rules0 nc0 res nc1 H Hwf; simpl in H.
  - injection H as _ <-. split; [exact Hwf | apply incl_refl].
  - destruct (compile_rule r nc0) as [[hr nc0']|] eqn:Hcr; cbn beta iota in H.
    + destruct (compile_rule_reg r all_rels nc0 hr nc0' Hcr Hwf) as [Hwf' Hmono].
      destruct (IH (hr :: rules0) nc0' res nc1 H Hwf') as [Hwf1 Hmono1].
      split; [exact Hwf1 | apply (incl_tran Hmono Hmono1)].
    + rewrite compile_node_fold_error in H. discriminate.
Qed.

(* MAIN registration fact: the node's trie table has duplicate-free trie ids, so [lookup_trie]
   returns exactly the trie for any registered id (see [lookup_trie_some]). *)
Lemma compile_node_wf (node : node_id) (prog : lowered_program) (all_rels : list rel_id)
    (ninfo : node_info) :
  compile_node node prog = Success ninfo ->
  NoDup (map (fun t => t.(tid)) ninfo.(ntries)).
Proof.
  unfold DistributedDatalogToHardwareCompiler.compile_node. intros H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[rules nc1]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (DistributedDatalogToHardwareCompiler.initial_node_context))
    by (split; [intros t [] | constructor]).
  destruct (compile_node_fold_wf all_rels prog [] (DistributedDatalogToHardwareCompiler.initial_node_context) rules nc1
              Hfold Hwf0) as [[_ Hnd] _].
  cbn [DistributedHardwareProgram.ntries]. rewrite map_rev. apply NoDup_rev. exact Hnd.
Qed.

End RegisterNode.

(*============================================================================*)
(*  Capstone: a compiled node implements its (lowered) datalog program.         *)
(*============================================================================*)

Section NodeCorrect.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context `{params : datalog_params (_rel := rel_id) (rel_eqb := nat_eqb) (rel_eqb_ok := nat_eqb_ok)}.
Context {var_idx_map : map.map exprvar nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map exprvar unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_graph_impl : graph.graph exprvar} {var_graph_impl_ok : graph.ok var_graph_impl}.
Context {node_id : node_idT}
        {node_id_eqb : node_id -> node_id -> bool}
        {node_id_eqb_spec : forall x y : node_id, BoolSpec (x = y) (x <> y) (node_id_eqb x y)}.
Context {node_id_set : map.map node_id unit}.
Context {forwarding_table : map.map (rel_id * fwd_from) (list fwd_to)}.
#[local] Existing Instance rel_id.

(* PER-RULE: a compiled rule (whose post-context tries are all in the node table [tries], which
   has unique ids) matches its lowered datalog rule -- by discharging every hypothesis of
   [hw_rule_correct] from the ordering / hypothesis / conclusion / registration lemmas. *)
Lemma compile_rule_matches (rule : lowered_rule) (all_rels : list rel_id) (nc nc' : node_context)
    (hr : hardware_rule) (tries : list trie) :
  bare_rule rule ->
  wf_nc nc ->
  compile_rule rule nc = Success (hr, nc') ->
  incl nc'.(nctries) tries ->
  NoDup (map (fun t => t.(tid)) tries) ->
  hw_rule_matches tries rule hr.
Proof.
  intros Hbare Hwf H Hincl Hndt.
  destruct rule as [rconcls rhyps | cr ag hyp_rel]; cbn in Hbare; [| contradiction].
  destruct Hbare as [Hbh Hbc].
  unfold DistributedDatalogToHardwareCompiler.compile_rule in H. cbv zeta in H.
  set (ord := compute_variable_ordering_ordered (create_dependency_graph rhyps) rhyps) in *.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_hyps ?a ?b ?c ?d] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_hyps a b c d) as [q nc''] eqn:Hch
  end.
  cbn beta iota zeta in H.
  match type of H with
  | context [DistributedDatalogToHardwareCompiler.compile_concls ?a ?b] =>
      destruct (DistributedDatalogToHardwareCompiler.compile_concls a b) as [concls|] eqn:Hcc
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <- <-.
  destruct (compile_hyps_full rhyps ord all_rels nc q nc'' Hch Hwf)
    as [_ [_ [tb [Hq [Hlentb [HFtt Htbin]]]]]].
  pose proof (compile_concls_corr rconcls all_rels ord concls Hbc Hcc) as Hconcl.
  destruct (compute_variable_ordering_ordered_correct rhyps Hbh) as [Hnd [Hsub Hcov]].
  apply (hw_rule_correct rconcls rhyps
           {| hhyps := q; hconcls := concls;
              hsig := map (fun h => (h.(Datalog.clause.rel), length h.(Datalog.clause.args))) rhyps |}
           ord tb tries {| tid := 0; trel := 0; tperm := [] |}
           {| Datalog.clause.rel := 0; Datalog.clause.args := [] |}).
  - exact Hnd.
  - exact Hbh.
  - exact Hbc.
  - exact Hlentb.
  - exact Hcov.
  - exact Hsub.
  - exact Hq.
  - reflexivity.
  - exact Hconcl.
  - intros i Hi.
    apply Forall2_nth_error_iff in HFtt. destruct HFtt as [_ Hpt].
    assert (Hitb : i < length tb) by (rewrite Hlentb; exact Hi).
    assert (Pt : nth_error tb i = Some (nth i tb {| tid := 0; trel := 0; tperm := [] |}))
      by (apply nth_error_nth'; exact Hitb).
    assert (Ph : nth_error rhyps i = Some (nth i rhyps {| Datalog.clause.rel := 0; Datalog.clause.args := [] |}))
      by (apply nth_error_nth'; exact Hi).
    specialize (Hpt i _ _ Pt Ph). destruct Hpt as [Htrel Htperm].
    split; [exact Htrel | split; [exact Htperm |]].
    apply lookup_trie_some; [|exact Hndt].
    apply Hincl. apply Htbin. apply nth_In. exact Hitb.
Qed.

(* The [compile_node] fold: every compiled rule matches its datalog rule against the node's
   final trie table (each rule's tries are a subset of the final table, by monotonicity). *)
Lemma compile_node_fold_matches (all_rels : list rel_id) (tries : list trie) (prog : lowered_program) :
  forall (rules0 : list hardware_rule) (nc0 : node_context)
         (compiled_rev : list hardware_rule) (nc_final : node_context),
  fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list) prog (Success (rules0, nc0))
    = Success (compiled_rev, nc_final) ->
  Forall bare_rule prog ->
  wf_nc nc0 -> incl nc_final.(nctries) tries -> NoDup (map (fun t => t.(tid)) tries) ->
  exists hrs, compiled_rev = (rev hrs ++ rules0)%list /\
              Forall2 (fun rule hr => hw_rule_matches tries rule hr) prog hrs.
Proof.
  induction prog as [|r prog IH];
    intros rules0 nc0 compiled_rev nc_final H Hbare Hwf Hincl Hndt; simpl in H.
  - injection H as <- <-. exists []. split; [reflexivity | constructor].
  - inversion Hbare as [|x l Hbr Hbprog]; subst.
    destruct (compile_rule r nc0) as [[hr nc0']|] eqn:Hcr; cbn beta iota in H.
    + destruct (compile_rule_reg r all_rels nc0 hr nc0' Hcr Hwf) as [Hwf' _].
      destruct (compile_node_fold_wf all_rels prog (hr :: rules0) nc0' compiled_rev nc_final H Hwf')
        as [_ Hmonotail].
      assert (Hinc' : incl nc0'.(nctries) tries) by (apply (incl_tran Hmonotail Hincl)).
      pose proof (compile_rule_matches r all_rels nc0 nc0' hr tries Hbr Hwf Hcr Hinc' Hndt) as Hm.
      destruct (IH (hr :: rules0) nc0' compiled_rev nc_final H Hbprog Hwf' Hincl Hndt)
        as [hrs [Hcomp HF]].
      exists (hr :: hrs). split.
      * simpl. rewrite Hcomp, <- app_assoc. reflexivity.
      * constructor; [exact Hm | exact HF].
    + rewrite compile_node_fold_error in H. discriminate.
Qed.

Lemma Forall2_map_lrule (tries : list trie) (prog : lowered_program) (hrs : list hardware_rule) :
  Forall2 (fun rule hr => hw_rule_matches tries rule hr) prog hrs ->
  Forall2 (hw_rule_matches tries) (prog) hrs.
Proof. intros HF. induction HF; simpl; constructor; assumption. Qed.

(* Per node: every compiled hardware rule matches its source rule against the node's trie table.
   This is exactly the per-node condition [ninfos_node_rules_match] needs. *)
Lemma compile_node_matches (node : node_id) (prog : lowered_program) (all_rels : list rel_id)
    (ninfo : node_info) :
  Forall bare_rule prog ->
  compile_node node prog = Success ninfo ->
  Forall2 (hw_rule_matches ninfo.(ntries)) (prog) ninfo.(nprogram).
Proof.
  intros Hbare H.
  pose proof (compile_node_wf node prog all_rels ninfo H) as Hndt.
  unfold DistributedDatalogToHardwareCompiler.compile_node in H.
  match type of H with
  | context [fold_left ?F prog ?init] =>
      destruct (fold_left F prog init) as [[compiled_rev nc_final]|] eqn:Hfold
  end; cbn beta iota zeta in H; [|discriminate].
  injection H as <-.
  assert (Hwf0 : wf_nc (DistributedDatalogToHardwareCompiler.initial_node_context))
    by (split; [intros t [] | constructor]).
  assert (Hincl : incl nc_final.(nctries) (rev nc_final.(nctries)))
    by (intros t Ht; rewrite <- in_rev; exact Ht).
  cbn [DistributedHardwareProgram.ntries] in Hndt, Hincl |- *.
  cbn [DistributedHardwareProgram.nprogram].
  destruct (compile_node_fold_matches all_rels (rev nc_final.(nctries)) prog []
              (DistributedDatalogToHardwareCompiler.initial_node_context) compiled_rev nc_final
              Hfold Hbare Hwf0 Hincl Hndt) as [hrs [Hcomp HF]].
  rewrite Hcomp, app_nil_r, rev_involutive.
  apply Forall2_map_lrule. exact HF.
Qed.

End NodeCorrect.

(*============================================================================*)
(*  Top-level [compile]: bridging its output back to per-node [compile_node].   *)
(*============================================================================*)

Section CompileTop.

Import ResultMonadNotations.
Open Scope result_monad_scope.

Context `{params : datalog_params (_rel := rel_id) (rel_eqb := nat_eqb) (rel_eqb_ok := nat_eqb_ok)}.
Context {var_idx_map : map.map exprvar nat} {var_idx_map_ok : map.ok var_idx_map}.
Context {var_node_set : map.map exprvar unit} {var_node_set_ok : map.ok var_node_set}.
Context {var_graph_impl : graph.graph exprvar} {var_graph_impl_ok : graph.ok var_graph_impl}.
Context {node_id : node_idT}
        {node_id_eqb : Eqb node_id} {node_id_eqb_spec : Eqb_ok node_id_eqb}.
#[local] Existing Instance rel_id.
Context {node_id_set : map.map node_id unit}.
Context {graph_node_id : graph.graph node_id}.
Context {graph_vnode : graph.graph vnode} {graph_vnode_ok : graph.ok graph_vnode}.
Context {forwarding_table : map.map (rel_id * fwd_from) (list fwd_to)} {forwarding_table_ok : map.ok forwarding_table}.
Context {layout_map : map.map node_id (@HardwareProgram.lowered_program exprvar fn aggregator)}
        {layout_map_ok : map.ok layout_map}.
Context {node_ftable_map : map.map node_id forwarding_table} {node_ftable_map_ok : map.ok node_ftable_map}.
Context {fact_locations_map : map.map rel_id (list node_id)}
        {fact_locations_map_ok : map.ok fact_locations_map}.
Context {rels_at_node : map.map node_id (list rel_id)}
        {rels_at_node_ok : map.ok rels_at_node}.


(* Every node_info produced by [compile_all_nodes] is the [compile_node] result for some node
   in the lowered layout. *)
Lemma compile_all_nodes_in (llayout : layout_map) (all_rels : list rel_id)
    (ninfos : list node_info) (ninfo : node_info) :
  compile_all_nodes llayout = Success ninfos ->
  In ninfo ninfos ->
  exists node lprog, map.get llayout node = Some lprog /\ compile_node node lprog = Success ninfo.
Proof.
  intros H Hin. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
  apply List.all_success_Success_iff, Forall2_map_l, Forall2_flip_iff in H.
  destruct (Forall2_In_l _ _ _ _ H Hin) as [[node lprog] [Htup Hcn]].
  exists node, lprog. split; [apply map.tuples_spec; exact Htup | exact Hcn].
Qed.

(* Every node that the lowered layout assigns a program to compiles successfully. *)
Lemma compile_all_nodes_success (llayout : layout_map)
    (ninfos : list node_info) (node : node_id) (lprog : lowered_program) :
  compile_all_nodes llayout = Success ninfos ->
  map.get llayout node = Some lprog ->
  exists ninfo, compile_node node lprog = Success ninfo.
Proof.
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
  apply List.all_success_Success_iff, Forall2_map_l in H.
  destruct (Forall2_In_l _ _ _ _ H (proj2 (map.tuples_spec _ _ _) Hget)) as [ninfo [_ Hcn]].
  exists ninfo. exact Hcn.
Qed.

(* The empty program compiles to an empty node. *)
Lemma compile_node_nil (node : node_id) :
  compile_node node [] =
    Success {| nid := node; nprogram := []; nforwarding := map.empty; ntries := [] |}.
Proof. reflexivity. Qed.

(* Every node's lowered program compiles successfully (assigned nodes by [compile_all_nodes],
   unassigned ones because the empty program trivially compiles). *)
Lemma compile_node_lprog_of (llayout : layout_map)
    (ninfos : list node_info) (n : node_id) :
  compile_all_nodes llayout = Success ninfos ->
  exists ninfo, compile_node n (get_or_default llayout n) = Success ninfo.
Proof.
  intros H. unfold get_or_default, get_or. Tactics.destruct_one_match.
  - eapply compile_all_nodes_success; eassumption.
  - eexists. apply compile_node_nil.
Qed.

(* [compile_node] always stamps the result with the node it was given. *)
Lemma compile_node_nid (node : node_id) (prog : lowered_program) (all_rels : list rel_id) (ni : node_info) :
  compile_node node prog = Success ni -> ni.(nid) = node.
Proof.
  unfold DistributedDatalogToHardwareCompiler.compile_node.
  destruct (fold_left _ prog _) as [[compiled_rules ncontext]|] eqn:Hf; cbn beta iota; [|discriminate].
  intros H. injection H as <-. reflexivity.
Qed.

(* Every node the lowered layout assigns to has its [compile_node] result in [compile_all_nodes]. *)
Lemma compile_all_nodes_in_fwd (llayout : layout_map) (all_rels : list rel_id)
    (ninfos : list node_info) (node : node_id) (lprog : lowered_program) :
  compile_all_nodes llayout = Success ninfos ->
  map.get llayout node = Some lprog ->
  exists ninfo, compile_node node lprog = Success ninfo /\ In ninfo ninfos.
Proof.
  intros H Hget. unfold DistributedDatalogToHardwareCompiler.compile_all_nodes in H.
  apply List.all_success_Success_iff, Forall2_map_l in H.
  destruct (Forall2_In_l _ _ _ _ H (proj2 (map.tuples_spec _ _ _) Hget)) as [ninfo [Hin Hcn]].
  exists ninfo. split; [exact Hcn | exact Hin].
Qed.

(* Each entry of the (all-node) attached list is either a layout node (same id/tries/program as its
   [compile_all_nodes] info) or a forwarding-only node (empty program/tries, id not in [ninfos0]). *)
Lemma attach_in_data (ninfos0 : list node_info) (ft : node_ftable_map) (x : node_info) :
  In x (attach_forwarding_tables ninfos0 ft) ->
  (exists ni0, In ni0 ninfos0 /\ x.(nid) = ni0.(nid)
     /\ x.(ntries) = ni0.(ntries) /\ x.(nprogram) = ni0.(nprogram))
  \/ (x.(nprogram) = [] /\ x.(ntries) = [] /\ (forall ni0, In ni0 ninfos0 -> ni0.(nid) <> x.(nid))).
Proof.
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables.
  rewrite in_app_iff. intros [Hin | Hin].
  - apply in_map_iff in Hin. destruct Hin as [ni0 [Heq Hin0]]. subst x. cbn.
    left. exists ni0. repeat split; [exact Hin0 | reflexivity..].
  - apply in_map_iff in Hin. destruct Hin as [n' [Heq Hn']]. subst x. cbn.
    right. split; [reflexivity | split; [reflexivity|]].
    apply filter_In in Hn'. destruct Hn' as [_ Hfilt]. apply Bool.negb_true_iff in Hfilt.
    intros ni0 Hin0 Hnid.
    assert (Hex : List.existsb (fun ni => eqb ni.(nid) n') ninfos0 = true).
    { apply existsb_exists. exists ni0. split; [exact Hin0|].
      rewrite Hnid. destruct (eqb_boolspec _ n' n'); congruence. }
    rewrite Hex in Hfilt. discriminate.
Qed.

(* KEY: the tries/program read off the returned [ninfos] for node [n] are exactly what [compile_node]
   produces for [n] -- i.e. pointwise equal to [compiled_hn]'s recompute.  (Forwarding is handled
   separately.)  This lets the network read off [ninfos] reuse the [compiled_hn] correctness. *)
Lemma find_ninfo_node (llayout : layout_map) (all_rels : list rel_id)
    (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id) :
  compile_all_nodes llayout = Success ninfos0 ->
  (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(ntries)
    = match compile_node n (get_or_default llayout n) with Success ni => ni.(ntries) | Failure _ => [] end
  /\ (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nprogram)
    = match compile_node n (get_or_default llayout n) with Success ni => ni.(nprogram) | Failure _ => [] end.
Proof.
  intros Hcan. unfold find_ninfo.
  destruct (List.find (fun ni => eqb ni.(nid) n) (attach_forwarding_tables ninfos0 ft))
    as [x|] eqn:Hfind.
  - apply List.find_some in Hfind. destruct Hfind as [Hxin Hxnid].
    destruct (eqb_boolspec _ x.(nid) n) as [Hxn|]; [|discriminate].
    destruct (attach_in_data ninfos0 ft x Hxin) as [[ni0' [Hin0' [Hnid' [Htr' Hpr']]]] | [Hpr [Htr Hno]]].
    + (* layout node: x's data = ni0' = compile_node n (get_or_default llayout n) *)
      destruct (compile_all_nodes_in llayout all_rels ninfos0 ni0' Hcan Hin0')
        as [node'' [lprog'' [Hgnode'' Hcn'']]].
      assert (Hnidni0 : ni0'.(nid) = node'') by exact (compile_node_nid node'' lprog'' all_rels ni0' Hcn'').
      assert (Hn2 : node'' = n) by (rewrite <- Hnidni0, <- Hnid'; exact Hxn).
      rewrite Hn2 in Hgnode'', Hcn''.
      rewrite (get_or_default_Some _ _ _ Hgnode''), Hcn''.
      rewrite Htr', Hpr'. split; reflexivity.
    + (* forwarding-only: no layout node with id n, so get_or_default llayout n = [] *)
      assert (Hgn : map.get llayout n = None).
      { destruct (map.get llayout n) as [lprog|] eqn:Hg; [|reflexivity].
        destruct (compile_all_nodes_in_fwd llayout all_rels ninfos0 n lprog Hcan Hg) as [ni0 [Hcn Hin0]].
        exfalso. apply (Hno ni0 Hin0).
        rewrite (compile_node_nid n lprog all_rels ni0 Hcn), Hxn. reflexivity. }
      rewrite (get_or_default_None _ _ Hgn). rewrite compile_node_nil. cbn.
      rewrite Hpr, Htr. split; reflexivity.
  - (* find = None: no entry with id n, so n is not a layout node either *)
    assert (Hgn : map.get llayout n = None).
    { destruct (map.get llayout n) as [lprog|] eqn:Hg; [|reflexivity].
      destruct (compile_all_nodes_in_fwd llayout all_rels ninfos0 n lprog Hcan Hg) as [ni0 [Hcn Hin0]].
      assert (Hin : In {| nid := ni0.(nid); nprogram := ni0.(nprogram);
                          nforwarding := get_or_default ft ni0.(nid); ntries := ni0.(ntries) |}
                       (attach_forwarding_tables ninfos0 ft)).
      { unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables. rewrite in_app_iff.
        left. apply in_map_iff. exists ni0. split; [reflexivity | exact Hin0]. }
      pose proof (List.find_none _ _ Hfind _ Hin) as Hfn. cbn in Hfn.
      rewrite (compile_node_nid n lprog all_rels ni0 Hcn) in Hfn.
      destruct (eqb_boolspec _ n n); congruence. }
    cbn. rewrite (get_or_default_None _ _ Hgn). rewrite compile_node_nil. cbn. split; reflexivity.
Qed.

(* Boolean version of [bare_fact]: every argument is a plain variable.  PARAMETRIC over the relation
   and function types -- bareness inspects only [expr.var]/[expr.app], never the relation/function
   identifiers -- so the SAME check applies to the source layout (over [rel]/[fn]) and the renamed
   lowered layout (over [rel_id]/[fn]). *)
Definition bare_factb {Rel Fn} (f : Datalog.clause (relt := Rel) (fn := Fn)) : bool :=
  forallb (fun e => match e with expr.var _ => true | expr.app _ _ => false end) f.(Datalog.clause.args).

Definition bare_ruleb {Rel Fn} (r : Datalog.rule (_rel := Rel) (_fn := Fn)) : bool :=
  match r with
  | Datalog.rule.impl concls hyps => forallb bare_factb hyps && forallb bare_factb concls
  | _ => false
  end.

Lemma bare_factb_spec (lf : lowered_fact) : bare_factb lf = true -> bare_fact lf.
Proof.
  unfold bare_factb, bare_fact. intros H. rewrite forallb_forall in H.
  apply Forall_forall. intros e He. specialize (H e He).
  destruct e as [v|f args]; [exists v; reflexivity | discriminate].
Qed.

Lemma bare_ruleb_spec (lr : lowered_rule) : bare_ruleb lr = true -> bare_rule lr.
Proof.
  destruct lr as [concls hyps | cr ag hr0]; cbn; [| intros HH; discriminate].
  intros H. apply andb_true_iff in H. destruct H as [H1 H2].
  rewrite forallb_forall in H1, H2. split.
  - apply Forall_forall. intros lf Hlf. apply bare_factb_spec. apply H1. exact Hlf.
  - apply Forall_forall. intros lf Hlf. apply bare_factb_spec. apply H2. exact Hlf.
Qed.

(* Decidable check that every program in a layout is bare.  PARAMETRIC over the relation/function
   types and the layout-map instance, so it applies to both the source [layout] and the lowered
   [llayout]. *)
Definition bare_layoutb {Rel Fn} {M : map.map node_id (list (Datalog.rule (_rel := Rel) (_fn := Fn)))}
    (lay : M) : bool :=
  map.fold (fun acc _ p => acc && forallb bare_ruleb p) true lay.

Lemma bare_layoutb_entry {Rel Fn} {M : map.map node_id (list (Datalog.rule (_rel := Rel) (_fn := Fn)))}
    {M_ok : map.ok M} (lay : M) :
  bare_layoutb lay = true ->
  forall n p, map.get lay n = Some p -> forallb bare_ruleb p = true.
Proof.
  unfold bare_layoutb.
  apply (map.fold_spec
    (fun (m : M) (b : bool) =>
       b = true -> forall n p, map.get m n = Some p -> forallb bare_ruleb p = true)).
  - intros _ n p Hget. rewrite map.get_empty in Hget. discriminate.
  - intros k v m r Hgmk IH Hb n p Hget.
    apply andb_true_iff in Hb. destruct Hb as [Hr Hv].
    destruct (eqb_boolspec _ n k) as [->|Hne].
    + rewrite map.get_put_same in Hget. injection Hget as <-. exact Hv.
    + rewrite map.get_put_diff in Hget by congruence.
      apply (IH Hr n p Hget).
Qed.

(* [bare_layoutb] soundly discharges conjunct (1) of [distributes]. *)
Lemma bare_layoutb_spec (llayout : layout_map) :
  bare_layoutb llayout = true ->
  forall n, Forall bare_rule (get_or_default llayout n).
Proof.
  intros H n. destruct (map.get llayout n) as [p|] eqn:Hget.
  - rewrite (get_or_default_Some _ _ _ Hget).
    apply Forall_forall. intros lr Hlr.
    pose proof (bare_layoutb_entry llayout H n p Hget) as Hp.
    rewrite forallb_forall in Hp. apply bare_ruleb_spec. apply Hp. exact Hlr.
  - rewrite (get_or_default_None _ _ Hget). constructor.
Qed.

(* [range_restricted_ruleb]: every variable in a rule's CONCLUSION also appears in some
   hypothesis -- the standard Datalog range-restriction/safety condition. Unlike [bare_ruleb],
   the compiler never checks this itself; but [compile_rule]'s [get_rule_var_index] lookup
   (locating each concl variable in the hypothesis-derived [rule_var_order]) can only succeed for
   rules that satisfy it. It's exactly the extra hypothesis a "the compiler always succeeds"
   theorem needs alongside [bare_ruleb]. PARAMETRIC over the relation/function types like
   [bare_ruleb], for the same reason (applies to both the source and lowered layout). *)
Definition range_restricted_ruleb {Rel Fn} (r : Datalog.rule (_rel := Rel) (_fn := Fn)) : bool :=
  match r with
  | Datalog.rule.impl concls hyps =>
    let hvars := flat_map Datalog.clause.vars hyps in
    forallb (fun concl => forallb (fun v => existsb (eqb v) hvars) (Datalog.clause.vars concl))
      concls
  | _ => false
  end.

Definition range_restricted_layoutb {Rel Fn} {M : map.map node_id (list (Datalog.rule (_rel := Rel) (_fn := Fn)))}
    (lay : M) : bool :=
  map.fold (fun acc _ p => acc && forallb range_restricted_ruleb p) true lay.

(* PENDING: not yet proven.  A bare, range-restricted layout whose forwarding tables pass the topology
   and routing checks on a valid topology always compiles successfully; i.e. the converse of
   [compile_distributed_correct]'s "given [compile ... = Success]" hypothesis.  The routing premise is
   spelled out exactly as [compile] computes it internally. *)
Theorem compile_succeeds (layout : layout_map) (outs ins : fact_locations_map)
    (ftables : node_ftable_map) (g : ComputableGraph node_id) :
  check_graph_valid g = true ->
  layout_in_graphb g layout = true ->
  ftables_in_graphb outs g ftables = true ->
  bare_layoutb layout = true ->
  range_restricted_layoutb layout = true ->
  check_ftables_routable ftables ins (get_all_producers_of layout (map.keys ins))
    (get_all_consumers_of layout (map.keys outs)) = Success tt ->
  exists ninfos, compile layout outs ins ftables g = Success ninfos.
Proof.
Admitted.

(*----Forwarding read off the returned [ninfos]----*)

(* Every attached node carries the forwarding table's entry for its id. *)
Lemma attach_nforwarding (ninfos0 : list node_info) (ft : node_ftable_map) (x : node_info) :
  In x (attach_forwarding_tables ninfos0 ft) ->
  x.(nforwarding) = get_or_default ft x.(nid).
Proof.
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables. rewrite in_app_iff.
  intros [Hin | Hin]; apply in_map_iff in Hin; destruct Hin as [a [Heq _]]; subst x; reflexivity.
Qed.

(* Every node that forwards anything (a key of the table) has a node_info in [ninfos]. *)
Lemma ft_key_in_attach (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id)
    (v : forwarding_table) :
  map.get ft n = Some v ->
  exists x, In x (attach_forwarding_tables ninfos0 ft) /\ x.(nid) = n.
Proof.
  intros Hget. assert (Hkey : In n (map.keys ft)) by exact (map.in_keys ft n v Hget).
  unfold DistributedDatalogToHardwareCompiler.attach_forwarding_tables.
  destruct (List.existsb (fun ni => eqb ni.(nid) n) ninfos0) eqn:Hex.
  - apply existsb_exists in Hex. destruct Hex as [ni0 [Hin0 Heqn]].
    destruct (eqb_boolspec _ ni0.(nid) n) as [Hni0n|]; [|discriminate].
    eexists. split.
    + rewrite in_app_iff. left. apply in_map_iff. exists ni0. split; [reflexivity | exact Hin0].
    + cbn. exact Hni0n.
  - eexists. split.
    + rewrite in_app_iff. right. apply in_map_iff. exists n. split; [reflexivity|].
      apply filter_In. split; [exact Hkey | apply Bool.negb_true_iff; exact Hex].
    + cbn. reflexivity.
Qed.

(* The forwarding table read off [ninfos] for node [n] is exactly the table's entry. *)
Lemma find_ninfo_nforwarding (ninfos0 : list node_info) (ft : node_ftable_map) (n : node_id) :
  (find_ninfo (attach_forwarding_tables ninfos0 ft) n).(nforwarding) = get_or_default ft n.
Proof.
  unfold find_ninfo.
  destruct (List.find (fun ni => eqb ni.(nid) n) (attach_forwarding_tables ninfos0 ft))
    as [x|] eqn:Hfind.
  - apply List.find_some in Hfind. destruct Hfind as [Hxin Hxnid].
    destruct (eqb_boolspec _ x.(nid) n) as [Hxn|]; [|discriminate].
    rewrite (attach_nforwarding ninfos0 ft x Hxin), Hxn. reflexivity.
  - assert (Hgn : map.get ft n = None).
    { destruct (map.get ft n) as [v|] eqn:Hg; [|reflexivity].
      destruct (ft_key_in_attach ninfos0 ft n v Hg) as [x [Hxin Hxn]].
      pose proof (List.find_none _ _ Hfind x Hxin) as Hfn. cbn in Hfn.
      rewrite Hxn in Hfn. destruct (eqb_boolspec _ n n); congruence. }
    cbn. unfold get_or_default, get_or. rewrite Hgn. reflexivity.
Qed.

Lemma forward_from_ninfos_attach (ninfos0 : list node_info) (ft : node_ftable_map)
    (n : node_id) (R : rel_id) (src : fwd_from) :
  forward_from_ninfos (attach_forwarding_tables ninfos0 ft) n R src
  = get_or_default (get_or_default ft n) (R, src).
Proof. unfold forward_from_ninfos. rewrite find_ninfo_nforwarding. reflexivity. Qed.

Lemma ninfos_node_rules_match (llayout : layout_map) (all_rels : list rel_id)
    (ninfos0 : list node_info) (ft : node_ftable_map) :
  compile_all_nodes llayout = Success ninfos0 ->
  (forall n, Forall bare_rule (get_or_default llayout n)) ->
  forall n, Forall2 (hw_rule_matches (node_tries (attach_forwarding_tables ninfos0 ft) n))
              (get_or_default llayout n)
              (node_prog (attach_forwarding_tables ninfos0 ft) n).
Proof.
  intros Hcan Hbare n.
  destruct (compile_node_lprog_of llayout ninfos0 n Hcan) as [ninfo Hcn].
  destruct (find_ninfo_node llayout all_rels ninfos0 ft n Hcan) as [Htr Hpr].
  rewrite Hcn in Htr, Hpr. cbn in Htr, Hpr.
  unfold DistributedHardwareSemantics.node_tries, DistributedHardwareSemantics.node_prog.
  rewrite Htr, Hpr.
  apply (compile_node_matches n (get_or_default llayout n) all_rels ninfo (Hbare n) Hcn).
Qed.

Lemma source_program_in (layout : layout_map) (r : Datalog.rule (_rel := rel_id) (_fn := fn)) :
  In r (source_program layout) <->
  exists n p, map.get layout n = Some p /\ In r p.
Proof. unfold source_program. apply In_concat_values. Qed.

(* The compiler's inverted internal maps [get_internal_{consumers,producers}_of] recover exactly the
   nodes with some rule that has [R] among its hypothesis/conclusion relations. *)
Lemma get_map_values (fr : lowered_program -> list rel_id) (m : layout_map) (n : node_id) :
  map.get (@map.map_values node_id lowered_program (list rel_id) layout_map rels_at_node fr m) n
  = option_map fr (map.get m n).
Proof.
  unfold map.map_values. revert n. eapply map.fold_spec.
  - intros n. rewrite !map.get_empty. reflexivity.
  - intros k0 v m0 acc Hget IH n. rewrite map.get_put_dec, IH, map.get_put_dec.
    destruct (eqb k0 n); reflexivity.
Qed.

Lemma in_internal_iff (fr : rule -> list rel_id) (llayout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (invert (map.map_values (fun p => dedup (flat_map fr p)) llayout)) R)
  <-> exists r, In r (get_or_default llayout n) /\ In R (fr r).
Proof.
  rewrite in_get_or_default_invert, get_map_values.
  destruct (map.get llayout n) as [p|] eqn:Hn; cbn [option_map].
  - rewrite (get_or_default_Some _ _ _ Hn). split.
    + intros [bs [Heq Hin]]. injection Heq as <-. rewrite dedup_In in Hin. apply in_flat_map in Hin. exact Hin.
    + intros [r [Hr HRr]]. exists (dedup (flat_map fr p)). split; [reflexivity|].
      rewrite dedup_In. apply in_flat_map. exists r. split; assumption.
  - rewrite (get_or_default_None _ _ Hn). split.
    + intros [bs [Heq _]]. discriminate.
    + intros [r [[] _]].
Qed.

(* [edb_routable lfp Q]: the base facts [Q] form a routable EDB for the declared input/producer
   locations [lfp] -- every [Q]-fact's relation has at least one declared input node, so the fact can
   actually enter the network.  (This is the EDB side condition of the top correctness theorem.) *)
Definition edb_routable (lfp : fact_locations_map) (Q : Datalog.fact (_rel := rel_id) -> Prop) : Prop :=
  forall f, Q f -> exists n, In n (get_or_default lfp (fact.rel f)).

Lemma node_consumes_internal (llayout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (get_internal_consumers_of llayout) R)
  <-> exists r, In r (get_or_default llayout n) /\ In R (rule.hyp_rels r).
Proof. unfold DistributedDatalogToHardwareCompiler.get_internal_consumers_of. apply in_internal_iff. Qed.

Lemma node_produces_internal (llayout : layout_map) (n : node_id) (R : rel_id) :
  In n (get_or_default (get_internal_producers_of llayout) R)
  <-> exists r, In r (get_or_default llayout n) /\ In R (rule.concl_rels r).
Proof. unfold DistributedDatalogToHardwareCompiler.get_internal_producers_of. apply in_internal_iff. Qed.

Lemma rule_in_source_program (layout : layout_map) (n : node_id) (r : Datalog.rule (_rel := rel_id) (_fn := fn)) :
  In r (get_or_default layout n) -> In r (source_program layout).
Proof.
  intros Hr. destruct (map.get layout n) as [p|] eqn:Hget.
  - apply source_program_in. exists n, p. rewrite (get_or_default_Some _ _ _ Hget) in Hr. auto.
  - rewrite (get_or_default_None _ _ Hget) in Hr. destruct Hr.
Qed.

Lemma In_get_or_default {K V} {M : map.map K (list V)} (m : M) (k : K) (x : V) :
  In x (get_or_default m k) -> exists l, map.get m k = Some l /\ In x l.
Proof.
  unfold get_or_default, get_or. destruct (map.get m k) as [l|]; [eauto | intros []].
Qed.

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

Lemma producer_internal (layout : layout_map) (ins_rels : list rel_id) (R : rel_id) (n : node_id)
    (r : Datalog.rule (_rel := rel_id) (_fn := fn)) :
  In r (get_or_default layout n) -> In R (rule.concl_rels r) ->
  In (vnode.at_port n fwd_from.self) (get_or_default (get_all_producers_of layout ins_rels) R).
Proof.
  intros Hr HR. unfold DistributedDatalogToHardwareCompiler.get_all_producers_of. cbv zeta.
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
  intros HR. unfold DistributedDatalogToHardwareCompiler.get_all_producers_of. cbv zeta.
  apply In_get_or_default_union_with. right.
  erewrite get_or_default_Some; [|apply get_of_list_const; exact HR]. left. reflexivity.
Qed.

Lemma consumer_internal (layout : layout_map) (outs_rels : list rel_id) (R : rel_id) (n : node_id)
    (r : Datalog.rule (_rel := rel_id) (_fn := fn)) :
  In r (get_or_default layout n) -> In R (rule.hyp_rels r) ->
  In (vnode.fact_dst n) (get_or_default (get_all_consumers_of layout outs_rels) R).
Proof.
  intros Hr HR. unfold DistributedDatalogToHardwareCompiler.get_all_consumers_of. cbv zeta.
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
  intros HR. unfold DistributedDatalogToHardwareCompiler.get_all_consumers_of. cbv zeta.
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
  unfold DistributedDatalogToHardwareCompiler.all_consumers_fed in Hfed.
  eapply map.get_forallb in Hfed; [|exact Hget].
  unfold DistributedDatalogToHardwareCompiler.all_consumers_fed_for_relation in Hfed.
  rewrite forallb_forall in Hfed. specialize (Hfed p Hp). cbv beta in Hfed.
  apply inclb_incl in Hfed. apply graph.get_reachable_nodes_spec, Hfed, Hcs.
Qed.

Lemma check_ftables_routable_fed (ftables : node_ftable_map) (ins : fact_locations_map)
    (producers consumers : partial_map rel_id (list vnode)) :
  check_ftables_routable ftables ins producers consumers = Success tt ->
  all_consumers_fed (fun R => graph.of_edges (graph_of_ftables_at (get_or_default ins R) ftables R))
    producers consumers = true.
Proof.
  unfold DistributedDatalogToHardwareCompiler.check_ftables_routable. cbv zeta.
  destruct (all_consumers_fed _ _ _); [reflexivity | discriminate].
Qed.

Section Routing.
Context (prog : node_id -> hardware_program) (tries : node_id -> list trie)
        (forward : node_id -> rel_id -> fwd_from -> list fwd_to) (ft : node_ftable_map)
        (Hfwd : forall n R src, forward n R src = get_or_default (get_or_default ft n) (R, src))
        (ins : fact_locations_map) (Q : Datalog.fact (_rel := rel_id) -> Prop).

Local Abbreviation input := (fun n (f : Datalog.fact (_rel := rel_id)) => Q f /\ In n (get_or_default ins (fact.rel f))).
Local Abbreviation reach := (dreach prog tries forward input).
Local Abbreviation vgraph R := (graph.of_edges (graph_of_ftables_at (get_or_default ins R) ft R)).

Definition holds_at (f : Datalog.fact (_rel := rel_id)) (v : vnode) : Prop :=
  match v with
  | vnode.at_port n src => exists c, reach c /\ c n src f
  | vnode.fact_dst n => present prog tries forward input n f
  | vnode.ext_input => Q f
  | vnode.ext_output => hw_run_output prog tries forward input f
  end.

Lemma vgraph_edge (R : rel_id) (u v : vnode) :
  graph.edge (vgraph R) u v ->
  (exists n src dst, u = vnode.at_port n src /\ v = vnode.target_of n dst /\
     In dst (get_or_default (get_or_default ft n) (R, src)))
  \/ (u = vnode.ext_input /\ exists i, In i (get_or_default ins R) /\ v = vnode.at_port i fwd_from.input).
Proof.
  rewrite graph.edge_of_edges. unfold DistributedDatalogToHardwareCompiler.graph_of_ftables_at.
  rewrite in_app_iff. intros [H | H].
  - left. apply in_flat_map in H. destruct H as [[n ftn] [Htup H]]. apply map.tuples_spec in Htup.
    unfold DistributedDatalogToHardwareCompiler.graph_of_ftable_at in H.
    apply in_flat_map in H. destruct H as [[[R' src] dsts] [Htup' H]]. apply map.tuples_spec in Htup'.
    revert H. destruct (eqb_boolspec _ R R') as [<-|_]; intros H; [|destruct H].
    apply in_map_iff in H. destruct H as [dst [Heq Hdst]]. injection Heq as <- <-.
    exists n, src, dst. split; [reflexivity|]. split; [reflexivity|].
    rewrite (get_or_default_Some _ _ _ Htup), (get_or_default_Some _ _ _ Htup'). exact Hdst.
  - right. apply in_map_iff in H. destruct H as [i [Heq Hi]]. injection Heq as <- <-. eauto.
Qed.

Lemma holds_at_edge (u v : vnode) (f : Datalog.fact (_rel := rel_id)) :
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

Lemma holds_at_reaches (u v : vnode) (f : Datalog.fact (_rel := rel_id)) :
  graph.reaches (vgraph (fact.rel f)) u v -> holds_at f u -> holds_at f v.
Proof. intros Hr Hu. eapply reaches_closed; [| exact Hu | exact Hr]. intros. eapply holds_at_edge; eauto. Qed.

Context (layout : layout_map) (outs : fact_locations_map).
Context (Hmatch : forall n, Forall2 (hw_rule_matches (tries n)) (get_or_default layout n) (prog n)).

Local Abbreviation P := {| program.rules := source_program layout; program.meta_rules := [] |}.

Lemma reach_sound (c : config) :
  reach c -> forall n src f, c n src f -> program.interp P Q f.
Proof.
  induction 1 as [|c c' Hr IH Hstep]; intros n0 src0 f0 Hc; [destruct Hc|].
  inversion Hstep as [n f Hin | n nf hyps Hfire Hhyps | n n' f src ch Hcnf Hfwd']; subst c';
    unfold cadd in Hc; (destruct Hc as [Hold | (-> & -> & ->)]; [exact (IH _ _ _ Hold)|]).
  - apply pftree.leaf. apply Hin.
  - apply (matches_step _ _ _ _ _ (Hmatch n)) in Hfire. apply Exists_exists in Hfire.
    destruct Hfire as [r [Hin Hri]].
    eapply pftree.step with (l := hyps).
    + constructor. apply Exists_exists. exists r. split; [exact (rule_in_source_program _ _ _ Hin) | exact Hri].
    + eapply Forall_impl; [exact Hhyps|]. intros h [s [Hs _]]. exact (IH _ _ _ Hs).
  - exact (IH _ _ _ Hcnf).
Qed.

Lemma run_output_sound (f : Datalog.fact (_rel := rel_id)) :
  hw_run_output prog tries forward input f -> program.interp P Q f.
Proof. intros (n & src & c & Hr & Hc & _). exact (reach_sound c Hr n src f Hc). Qed.

Context (Hfed : all_consumers_fed (fun R => vgraph R)
                  (get_all_producers_of layout (map.keys ins))
                  (get_all_consumers_of layout (map.keys outs)) = true).
Context (HQ : edb_routable ins Q).

Lemma derivable_at_producer (f : Datalog.fact (_rel := rel_id)) :
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
    assert (Hpres : Forall (fun h => present prog tries forward input n h) l).
    { apply Forall_forall. intros h Hh. rewrite Forall_forall in IH.
      destruct (IH h Hh) as [p [Hp Hhp]].
      apply (holds_at_reaches p (vnode.fact_dst n) h); [|exact Hhp].
      apply (fed_reaches _ _ _ (fact.rel h) p (vnode.fact_dst n) Hfed Hp).
      apply (consumer_internal layout _ _ n r Hrn).
      apply rule.interp_hyp_relname_in in Hr. rewrite Forall_forall in Hr. exact (Hr h Hh). }
    destruct (present_list prog tries forward input n l Hpres) as [c [Hrc Hcl]].
    exists (vnode.at_port n fwd_from.self). split.
    + exact (producer_internal layout _ _ n r Hrn (rule.interp_concl_relname_in _ _ _ Hr)).
    + exists (cadd c n fwd_from.self (fact.normal nf)). split.
      * eapply dreachS; [exact Hrc|]. eapply dstep_run; [|exact Hcl].
        apply (matches_step _ _ _ _ _ (Hmatch n)). apply Exists_exists. exists r. split; [exact Hrn | exact Hr].
      * unfold cadd. right. auto.
Qed.

Lemma derivable_output (f : Datalog.fact (_rel := rel_id)) :
  program.interp P Q f -> (exists n, In n (get_or_default outs (fact.rel f))) ->
  hw_run_output prog tries forward input f.
Proof.
  intros Hf [n Hn]. destruct (derivable_at_producer f Hf) as [p [Hp Hfp]].
  apply (holds_at_reaches p vnode.ext_output f); [|exact Hfp].
  apply (fed_reaches _ _ _ (fact.rel f) p vnode.ext_output Hfed Hp).
  apply consumer_output. exact (In_keys_of_In_get_or_default _ _ _ Hn).
Qed.

End Routing.

Lemma compile_success_extract (layout : layout_map) (outs ins : fact_locations_map)
    (ftables : node_ftable_map) (g : ComputableGraph node_id) (ninfos : list node_info) :
  compile layout outs ins ftables g = Success ninfos ->
  exists ninfos0,
    ninfos = attach_forwarding_tables ninfos0 ftables /\
    compile_all_nodes layout = Success ninfos0 /\
    check_ftables_routable ftables ins (get_all_producers_of layout (map.keys ins))
      (get_all_consumers_of layout (map.keys outs)) = Success tt.
Proof.
  intros H. unfold DistributedDatalogToHardwareCompiler.compile in H. cbv zeta in H.
  destruct (check_graph_valid g); cbn beta iota in H; [|discriminate].
  destruct (layout_in_graphb g layout); cbn beta iota in H; [|discriminate].
  destruct (ftables_in_graphb outs g ftables); cbn beta iota in H; [|discriminate].
  destruct (check_ftables_routable ftables ins (get_all_producers_of layout (map.keys ins))
              (get_all_consumers_of layout (map.keys outs))) as [[]|] eqn:Hroute;
    cbn beta iota in H; [|discriminate].
  destruct (compile_all_nodes layout) as [ninfos0|] eqn:Hcan; cbn beta iota in H; [|discriminate].
  injection H as <-. eauto.
Qed.

Theorem compile_distributed_correct
    (layout : layout_map) (outs ins : fact_locations_map) (ftables : node_ftable_map)
    (g : ComputableGraph node_id) (ninfos : list node_info) (Q : Datalog.fact (_rel := rel_id) -> Prop) :
  compile layout outs ins ftables g = Success ninfos ->
  bare_layoutb layout = true ->
  edb_routable ins Q ->
  forall f, (exists n, In n (get_or_default outs (fact.rel f))) ->
    run_ninfos ninfos (fun n f0 => Q f0 /\ In n (get_or_default ins (fact.rel f0))) f
    <-> program.interp {| program.rules := source_program layout; program.meta_rules := [] |} Q f.
Proof.
  intros Hcomp Hbare HQ f Hout.
  destruct (compile_success_extract layout outs ins ftables g ninfos Hcomp) as [ninfos0 [-> [Hcan Hroute]]].
  pose proof (ninfos_node_rules_match layout [] ninfos0 ftables Hcan (bare_layoutb_spec layout Hbare)) as Hmatch.
  pose proof (forward_from_ninfos_attach ninfos0 ftables) as Hfwd.
  pose proof (check_ftables_routable_fed _ _ _ _ Hroute) as Hfed.
  unfold run_ninfos. split.
  - eapply run_output_sound; eassumption.
  - intros Hf. eapply derivable_output; eassumption.
Qed.

Context {rel : relT} {rel_eqb : Eqb rel} {rel_eqb_ok : Eqb_ok rel_eqb}.


Definition program_rels (p : list (@Datalog.rule rel exprvar fn aggregator)) : list rel :=
  flat_map rule.all_rels p.

Local Abbreviation rules_only p := {| program.rules := p; program.meta_rules := [] |}.

Definition relabel_Q (rho : rel -> rel_id) (Q : Datalog.fact (_rel := rel) -> Prop)
    : Datalog.fact (_rel := rel_id) -> Prop :=
  fun f' => exists f, f' = fact.map_rel rho f /\ Q f.

Theorem nattify_and_compile_correct
    (p : list (@Datalog.rule rel exprvar fn aggregator))
    (layout : layout_map) (outs ins : fact_locations_map) (ftables : node_ftable_map)
    (g : ComputableGraph node_id) (ninfos : list node_info)
    (Qsrc : Datalog.fact (_rel := rel) -> Prop) (fsrc : Datalog.fact (_rel := rel)) :
  compile layout outs ins ftables g = Success ninfos ->
  bare_layoutb layout = true ->
  DistributedDatalogToHardwareCompiler.layout_distributes_program
    (NattifyRel.nattify_rel_prog (program_rels p) (rules_only p)).(program.rules) layout ->
  (forall f, Qsrc f -> In (fact.rel f) (program_rels p)) ->
  edb_routable ins (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc) ->
  (exists n, In n (get_or_default outs (fact.rel (nattify_rel_fact (program_rels p) (rules_only p) fsrc)))) ->
  ( run_ninfos ninfos
      (fun n f0 => relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc f0
                   /\ In n (get_or_default ins (fact.rel f0)))
      (nattify_rel_fact (program_rels p) (rules_only p) fsrc)
    <-> program.interp (rules_only p) Qsrc fsrc ).
Proof.
  intros Hcomp Hbare Hdist Hscope Hedb Houtrel.
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
    [ exact (compile_distributed_correct layout outs ins ftables g ninfos
               (relabel_Q (encode_rel (rel_table (program_rels p) (rules_only p))) Qsrc)
               Hcomp Hbare Hedb
               (nattify_rel_fact (program_rels p) (rules_only p) fsrc) Houtrel)
    | ].
  eapply iff_trans; [ exact HB | ].
  symmetry.
  apply (nattify_rel_correct (program_rels p) (rules_only p) Qsrc fsrc Hscope).
Qed.

End CompileTop.
