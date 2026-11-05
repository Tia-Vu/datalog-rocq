From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb Permutation.
From DatalogRocq Require Import HardwareProgram.

Import ListNotations.

Section NodeHardwareSemantics.

(* Relation names are already numeric ([rel_id] = [nat]) at this stage; functions,
   variables, and the value type stay abstract. *)
Context `{params : datalog_params (_rel := rel_id)}.

Abbreviation dl_rule := (rule (_rel := rel_id)).
Abbreviation dl_fact := (Datalog.fact (_rel := rel_id)).

(*============================================================================*)
(*  Correctness: trie-join semantics vs. datalog semantics                    *)
(*============================================================================*)

(* Per-rule bridge: hardware rule [hr] (with trie table [tries]) is *correct* for datalog rule
   [r] when, fact-for-fact, the trie-join produces exactly what [r] produces.  Everything else
   reduces to this; [DistributedDatalogToHardwareCompilerCorrect] discharges it for compiled rules
   via the trie-join argument. *)
Definition hw_rule_matches (tries : list trie) (r : dl_rule) (hr : hardware_rule) : Prop :=
  forall nf hyps', hw_rule_impl tries hr nf hyps' <-> rule.interp r nf hyps'.

(* Pointwise, the two one-step relations agree once every rule matches. *)
Lemma matches_step (tries : list trie) (P : dl_program) (hp : hardware_program) nf hyps' :
  Forall2 (hw_rule_matches tries) P hp ->
  (Exists (fun hr => hw_rule_impl tries hr nf hyps') hp
   <-> Exists (fun r => rule.interp r nf hyps') P).
Proof.
  intros HF. induction HF as [| r hr P' hp' Hmatch HF IH]; simpl.
  - split; intros HE; inversion HE.
  - rewrite !Exists_cons. rewrite IH, (Hmatch nf hyps'). reflexivity.
Qed.

End NodeHardwareSemantics.

(*============================================================================*)
(*  Sanity checks on the index/permutation logic                              *)
(*============================================================================*)

(* [tperm] sends original arg position -> trie level; [inv_perm_index] inverts it. *)
Compute inv_perm_index [1; 0] 0.   (* level 0 lives at original position 1 => Some 1 *)
Compute inv_perm_index [1; 0] 1.   (* level 1 lives at original position 0 => Some 0 *)
Compute inv_perm_index [0; 1] 1.   (* identity perm => Some 1 *)

(* trie storing relation tuple [10; 20] under perm [1;0] (columns swapped):
   reading level 0 recovers original column 1 (= 20), level 1 recovers column 0 (= 10). *)
Compute trie_read (_value := nat) [1; 0] [10; 20] 0.   (* Some 20 *)
Compute trie_read (_value := nat) [1; 0] [10; 20] 1.   (* Some 10 *)

Compute zip3 [0; 1] [1; 1] [0; 1].

(* Projecting a binding [v0;v1;v2] = [7;8;9] through output indices [2;0] => (R, [9;7]). *)
Compute join_output_fact (_value := nat) [7; 8; 9]
  {| output_rel := 5; output_var_indices := [2; 0] |}.
