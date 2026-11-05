From Datalog Require Import Datalog Util.Permutation List Eqb Map Default.
From Stdlib Require Import List String Bool ZArith Sorting.Sorted Sorting.Permutation Lia.
From coqutil Require Import Datatypes.List Map.Interface OrderToPermutation Eqb.
From DatalogRocq Require Import DependencyGenerator MapInstances Topologies.Graph ComputableGraph.

Open Scope bool_scope.
Import ListNotations.

#[local] Instance var_idx : exprvarT := nat.
#[local] Instance rel_id : relT := nat.
#[local] Instance no_fns : fnT := Empty_set.
#[local] Instance no_agg : aggregatorT := Empty_set.

Definition var_of_expr (e : expr) :=
  match e with
  | expr.var v => v
  | expr.app f _ => match f with end
  end.

Lemma expr_var_of_expr e : expr.var (var_of_expr e) = e.
Proof. destruct e as [|[]]. reflexivity. Qed.

Lemma map_var_of_expr es : map expr.var (map var_of_expr es) = es.
Proof. rewrite map_map, map_ext with (g := fun e => e) by exact expr_var_of_expr. apply map_id. Qed.

Definition good_rule (r : rule) :=
  match r with
  | rule.impl _ hyps => Forall (fun c => NoDup (map var_of_expr c.(clause.args))) hyps
  | rule.agg _ _ _ => False
  end.

Definition permutation := list nat.

Module trie.
  Record trie := mk {
      rel : rel_id;
      (*column_order[i] is the column of the relation represented by level i of the trie,
        so [apply_permutation column_order things_in_relation_order] yields [things_in_trie_order] *)
      column_order : permutation;
    }.

  Scheme Boolean Equality for trie.
  #[export] Instance eqb : Eqb trie := trie_beq.
  #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.

  Definition interp (t : trie) (vars : list var_idx) (c : clause) :=
    c = {| clause.rel := t.(rel);
          clause.args := map expr.var (apply_permutation (invert_permutation t.(column_order)) vars) |}.

  Definition of_clause (c : clause) :=
    {| rel := c.(clause.rel);
      column_order := order_to_permutation (map var_of_expr c.(clause.args)) |}.

  Lemma interp_of_clause c :
    let vars := map var_of_expr c.(clause.args) in
    interp (of_clause c) (apply_permutation (order_to_permutation vars) vars) c.
  Proof.
    cbv [interp of_clause]. cbn [rel column_order].
    rewrite apply_invert_permutation by apply order_to_permutation_is_Permutation.
    rewrite map_var_of_expr. destruct c. reflexivity.
  Qed.

  Definition of_rule (r : rule) :=
    match r with
    | rule.impl _ hyps => map of_clause hyps
    | rule.agg _ a _ => match a with end
    end.

  Definition of_rules (rs : list rule) :=
    dedup eqb (flat_map of_rule rs).

End trie. Export (hints) trie. Abbreviation trie := trie.trie.
#[export] Register Scheme trie.eqb as beq for trie.trie.

Definition trie_id := nat.

(*TODO use sort (dedup l) instead?*)
Definition nats_in_list (l : list nat) :=
  filter (fun v => inb v l) (seq O (S (list_max l))).

Lemma nats_in_list_order l :
  NoDup l -> nats_in_list l = apply_permutation (order_to_permutation l) l.
Proof.
  intros Hl. apply sorted_le_perm_eq.
  - apply StronglySorted_Sorted, StronglySorted_filter, StronglySorted_seq.
  - apply Sorted_apply_order_to_permutation.
  - eapply Permutation_trans.
    + apply Permutation_filter_mem; [assumption | apply seq_NoDup |].
      intros x Hx. apply in_seq.
      pose proof (proj1 (list_max_le l _) (le_n _)) as Hmax. rewrite Forall_forall in Hmax.
      specialize (Hmax x Hx). lia.
    + apply apply_permutation_is_Permutation, order_to_permutation_is_Permutation.
Qed.

Module trie_hyp.
  Record trie_hyp := mk {
      trie : trie_id;
      var_set : list var_idx;
    }.

  Definition interp (tries : trie_id -> option trie.trie) (th : trie_hyp) (c : clause) :=
    exists t, tries th.(trie) = Some t /\ trie.interp t (nats_in_list th.(var_set)) c.

  Definition of_clause (tries : list trie.trie) (hyp : clause) : trie_hyp :=
    {| trie_hyp.trie := unwrap_or O (index_of (trie.of_clause hyp) tries) ;
      trie_hyp.var_set := map var_of_expr hyp.(clause.args) |}.

  Lemma interp_of_clause ts c :
    In (trie.of_clause c) ts ->
    NoDup (map var_of_expr c.(clause.args)) ->
    interp (nth_error ts) (of_clause ts c) c.
  Proof.
    intros Hin Hnd. destruct (index_of_In _ _ Hin) as (i & Hi & Hnth).
    cbv [interp of_clause]. cbn [trie var_set]. rewrite Hi.
    exists (trie.of_clause c). split; [exact Hnth|].
    rewrite nats_in_list_order by assumption. apply trie.interp_of_clause.
  Qed.

  Lemma interp_functional tries th c1 c2 :
    interp tries th c1 -> interp tries th c2 -> c1 = c2.
  Proof. intros (t1 & H1 & ->) (t2 & H2 & ->). congruence. Qed.

End trie_hyp. Abbreviation trie_hyp := trie_hyp.trie_hyp.

Module trie_rule.
  Record trie_rule := mk {
      concls : list clause;
      hyps : list trie_hyp;
    }.

  Definition interp (tries : trie_id -> option trie.trie) (t : trie_rule) (r : rule) :=
    exists hyps',
      r = rule.impl t.(concls) hyps' /\
        Forall2 (trie_hyp.interp tries) t.(hyps) hyps'.

  Definition of_rule (tries : list trie) (r : rule) :=
    match r with
    | rule.impl concls hyps => trie_rule.mk concls (map (trie_hyp.of_clause tries) hyps)
    | rule.agg _ a _ => match a with end
    end.

  Definition of_rules (rs : list rule) :=
    map (of_rule (trie.of_rules rs)) rs.

  Lemma interp_of_rule ts cs hs :
    Forall (fun c => In (trie.of_clause c) ts /\ NoDup (map var_of_expr c.(clause.args))) hs ->
    interp (nth_error ts) (of_rule ts (rule.impl cs hs)) (rule.impl cs hs).
  Proof.
    intros H. exists hs. split; [reflexivity|]. cbn [of_rule hyps].
    rewrite <- Forall2_map_l. apply Forall2_same. eapply Forall_impl; [|exact H].
    intros c [? ?]. apply trie_hyp.interp_of_clause; assumption.
  Qed.

  Lemma interp_of_rules rs :
    Forall good_rule rs ->
    Forall2 (interp (nth_error (trie.of_rules rs))) (of_rules rs) rs.
  Proof.
    intros H. unfold of_rules. rewrite <- Forall2_map_l. apply Forall2_same. rewrite Forall_forall in *. intros r Hr.
    specialize (H r Hr). destruct r as [cs hs|]; cbn in H; [|contradiction].
    apply interp_of_rule. rewrite Forall_forall in *. intros c Hc. split; [|auto].
    apply dedup_In, in_flat_map. exists (rule.impl cs hs). split; [assumption|].
    apply in_map, Hc.
  Qed.

  Lemma interp_of_rule_in rs r :
    Forall good_rule rs -> In r rs ->
    interp (nth_error (trie.of_rules rs)) (of_rule (trie.of_rules rs) r) r.
  Proof.
    intros H Hr. rewrite Forall_forall in H. pose proof (H r Hr) as Hg.
    destruct r as [cs hs|]; cbn in Hg; [|contradiction].
    apply interp_of_rule. rewrite Forall_forall in *. intros c Hc. split; [|auto].
    apply dedup_In, in_flat_map. exists (rule.impl cs hs). split; [assumption|].
    apply in_map, Hc.
  Qed.

  Lemma interp_functional tries t r1 r2 :
    interp tries t r1 -> interp tries t r2 -> r1 = r2.
  Proof.
    intros (hs1 & -> & H1) (hs2 & -> & H2). f_equal.
    revert hs2 H2. induction H1 as [|th c1 ths cs1 Hc1 _ IH]; intros hs2 H2; inversion H2; subst; [reflexivity|].
    f_equal; eauto using trie_hyp.interp_functional.
  Qed.

End trie_rule. Abbreviation trie_rule := trie_rule.trie_rule.
