From Datalog Require Import Datalog.
From Stdlib Require Import List String Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties.
From DatalogRocq Require Import DependencyGenerator MapInstances Topologies.Graph ComputableGraph.

Open Scope bool_scope.
Import ListNotations.

#[local] Instance var_idx : exprvarT := nat.
#[local] Instance rel_id : relT := nat.
#[local] Instance no_fns : fnT := Empty_set.

Definition permutation := list nat.

Module trie.
  Record trie := {
      rel : rel_id;
      perm : permutation;
    }.
End trie. Abbreviation trie := trie.trie.

Definition trie_id := nat.

Module trie_hyp.
  Record trie_hyp := {
      trie : trie_id;
      var_set : list var_idx;
    }.
End trie_hyp. Abbreviation trie_hyp := trie_hyp.trie_hyp.

Module trie_rule.
  Record trie_rule := {
      concls : list clause;
      hyps : list trie_hyp;
    }.
End trie_rule. Abbreviation trie_rule := trie_rule.trie_rule.
