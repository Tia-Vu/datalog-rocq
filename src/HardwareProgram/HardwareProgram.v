From Datalog Require Import Datalog Util.Permutation List Eqb Map.
From Stdlib Require Import List String Bool ZArith.
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

  Definition of_rule (r : rule) :=
    match r with
    | rule.impl _ hyps => map of_clause hyps
    | rule.agg _ _ _ => [] (*garbage*)
    end.

End trie. Export (hints) trie. Abbreviation trie := trie.trie.
#[export] Register Scheme trie.eqb as beq for trie.trie.

Definition trie_id := nat.

(*TODO use sort (dedup l) instead?*)
Definition nats_in_list (l : list nat) :=
  filter (fun v => inb v l) (seq O (S (list_max l))).

Module trie_hyp.
  Record trie_hyp := mk {
      trie : trie_id;
      var_set : list var_idx;
    }.

  Definition interp (tries : trie_id -> option trie.trie) (th : trie_hyp) (c : clause) :=
    exists t, tries th.(trie) = Some t /\ trie.interp t (nats_in_list th.(var_set)) c.

  Definition of_clause {mp : map.map trie.trie trie_id}
    (tries_inv : partial_map trie.trie trie_id) (hyp : clause) : trie_hyp :=
    {| trie_hyp.trie := get_or O tries_inv (trie.of_clause hyp) ;
      trie_hyp.var_set := map var_of_expr hyp.(clause.args) |}.

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

  Definition of_rule {mp : map.map trie.trie trie_id}
    (tries_inv : partial_map trie trie_id) (r : rule) :=
    match r with
    | rule.impl concls hyps => trie_rule.mk concls (map (trie_hyp.of_clause tries_inv) hyps)
    | rule.agg _ _ _ => trie_rule.mk [] [] (*garbage*)
    end.

  Definition of_rules {mp : map.map trie.trie trie_id} (rs : list rule) :=
    let tries := map.of_list (map swap (enumerate O (dedup eqb (flat_map trie.of_rule rs)))) in
    map (of_rule tries) rs.

End trie_rule. Abbreviation trie_rule := trie_rule.trie_rule.
