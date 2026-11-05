From Datalog Require Import Datalog Util.Permutation.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface OrderToPermutation.
From DatalogRocq Require Import DependencyGenerator MapInstances Topologies.Graph ComputableGraph.

Open Scope bool_scope.
Import ListNotations.

#[local] Instance var_idx : exprvarT := nat.
#[local] Instance rel_id : relT := nat.
#[local] Instance no_fns : fnT := Empty_set.
#[local] Instance no_agg : aggregatorT := Empty_set.

Definition permutation := list nat.

Module trie.
  Record trie := mk {
      rel : rel_id;
      (*column_order[i] is the column of the relation represented by level i of the trie,
        so [apply_permutation column_order things_in_trie_order] yields [things_in_relation_order] *)
      column_order : permutation;
    }.
End trie. Abbreviation trie := trie.trie.

Definition trie_id := nat.

Module trie_hyp.
  Record trie_hyp := mk {
      trie : trie_id;
      var_set : list var_idx;
    }.

  Definition interp (tries : trie_id -> option trie.trie) (th : trie_hyp) (c : clause) :=
    exists t,
      tries th.(trie) = Some t /\
        c = {| clause.rel := t.(trie.rel);
              clause.args := map expr.var (invert_permutation t.(trie.column_order)); |}.

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
End trie_rule. Abbreviation trie_rule := trie_rule.trie_rule.
