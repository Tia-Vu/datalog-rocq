(* A worked example / test of the single-node trie-join semantics ([NodeHardwareSemantics]),
   driven by the ACTUAL compiler.

   We take the source rule    J(x, y)  :-  A(x, y),  B(y, x)
   write it as a one-rule string-datalog program, COMPILE it with [compile_program] onto a 1x1
   grid, and read the generated tries / trie-join rule straight off the compiler's output.  Then
   we run [NodeHardwareSemantics] on those generated tries and the inputs A(7,8), B(8,7), and
   prove the node derives J(7,8).

   The compiler assigns relation ids in first-seen order over [concl_rels ++ hyp_rels]: J = 0,
   A = 1, B = 2.  It orders the
   join variables (y, x) (last-occurrence over the body A(x,y), B(y,x)); B already stores its
   columns in that order, but A -- stored (x,y) -- gets the non-trivial column permutation
   [1;0].  [trie_read] inverts it, so "level i" always means the i-th variable in the ordering
   regardless of where it physically sits.

   This file is a test in the repo's sense: it must type-check.  A successful build IS the test. *)

From Stdlib Require Import List String.
From Datalog Require Import Datalog.
From coqutil Require Import Result.
From DatalogRocq Require Import HardwareProgram NodeHardwareSemantics DistributedHardwareProgram
  DistributedHardwareSemantics StringDatalogParams StringGridCompiler DistributedDatalogToHardwareCompiler
  GridGraph GridTopology SortedListNat.
Import ListNotations.

(*==========================================================================*)
(*  The source rule and its compilation.                                      *)
(*==========================================================================*)

Open Scope string_scope.

(* J(x, y) :- A(x, y), B(y, x).  Head first, then the two body clauses. *)
Definition ruleJ : @Datalog.rule string string string unit :=
  Datalog.normal_rule
    [ {| Datalog.clause_rel := "J"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ]
    [ {| Datalog.clause_rel := "A"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ;
      {| Datalog.clause_rel := "B"; Datalog.clause_args := [Datalog.var_expr "y"; Datalog.var_expr "x"] |} ].

Definition jprog   : list (@Datalog.rule string string string unit) := [ruleJ].
Definition jlayout : list (node_id * list nat)      := [ ([0; 0]%nat, [0]%nat) ].  (* rule 0 -> node (0,0) *)
Definition jtopo   : GridGraph.Dimensions           := [1; 1]%nat.                  (* a 1x1 grid *)
Definition jio                                       := all_io_locations jprog jlayout jtopo.

(* Run the real end-to-end compiler. *)
Definition jcompiled := compile_program jprog jlayout jio jio jtopo.

(* The tries and trie-join program the compiler emitted for the (only) node. *)
Definition gen_tries : list trie :=
  match jcompiled with Success (n :: _) => ntries n    | _ => [] end.
Definition gen_prog : hardware_program :=
  match jcompiled with Success (n :: _) => nprogram n  | _ => [] end.

(*==========================================================================*)
(*  What the compiler generated (literals, so the values are visible) ...     *)
(*  ... and a proof that they are EXACTLY the compiler's output.              *)
(*==========================================================================*)

Definition trieA : trie := {| tid := 0; trel := 1; tperm := [1; 0] |}.  (* A stores (x,y); ordering (y,x): swapped   *)
Definition trieB : trie := {| tid := 1; trel := 2; tperm := [0; 1] |}.  (* B stores (y,x); ordering (y,x): identity *)
Definition tries : list trie := [trieA; trieB].

Definition joinY : join :=
  {| HardwareProgram.tries := [0; 1]; trie_levels := [0; 0]; clauses := [0; 1] |}.  (* y, level 0 *)
Definition joinX : join :=
  {| HardwareProgram.tries := [0; 1]; trie_levels := [1; 1]; clauses := [0; 1] |}.  (* x, level 1 *)

Definition concl : join_output := {| output_rel := 0; output_var_indices := [1; 0] |}.  (* J(x,y): x=level 1, y=level 0 *)

Definition hrJ : hardware_rule :=
  {| hhyps := [joinY; joinX]; hconcls := [concl]; hsig := [(1, 2); (2, 2)] |}.
Definition hp : hardware_program := [hrJ].

(* The compiler really does generate these tries and this trie-join rule from [ruleJ]. *)
Example tries_generated : gen_tries = tries.
Proof. vm_compute. reflexivity. Qed.
Example rule_generated : gen_prog = hp.
Proof. vm_compute. reflexivity. Qed.

(*==========================================================================*)
(*  Inputs and target.  The generated tries are purely numeric (no value      *)
(*  type), so we instantiate the run with [nat] values for readability.       *)
(*==========================================================================*)

Definition factA : @Datalog.fact rel_id nat := Datalog.normal_fact 1 [7; 8].  (* A(7,8) *)
Definition factB : @Datalog.fact rel_id nat := Datalog.normal_fact 2 [8; 7].  (* B(8,7) *)
Definition hyps' : list (@Datalog.fact rel_id nat) := [factA; factB].
Definition factJ : @Datalog.fact rel_id nat := Datalog.normal_fact 0 [7; 8].  (* J(7,8) *)

(*==========================================================================*)
(*  Layer 1: the permutation reads ([inv_perm_index] / [trie_read]).          *)
(*==========================================================================*)

(* Inverting A's swapped trie: level 0 lives at original column 1. *)
Example ex_inv_perm : inv_perm_index [1; 0] 0 = Some 1 := eq_refl.

(* Reading A's stored tuple [7;8] (= (x,y)) under ordering (y,x): level 0 recovers y = 8, level 1 recovers x = 7. *)
Example ex_read_Ay : trie_read (T := nat) [1; 0] [7; 8] 0 = Some 8 := eq_refl.
Example ex_read_Ax : trie_read (T := nat) [1; 0] [7; 8] 1 = Some 7 := eq_refl.

(* Reading B's stored tuple [8;7] (= (y,x)) with the identity permutation. *)
Example ex_read_By : trie_read (T := nat) [0; 1] [8; 7] 0 = Some 8 := eq_refl.
Example ex_read_Bx : trie_read (T := nat) [0; 1] [8; 7] 1 = Some 7 := eq_refl.

(*==========================================================================*)
(*  Layer 2: projecting the conclusion ([join_output_fact]).                  *)
(*==========================================================================*)

(* Binding [y;x] = [8;7] projected through output indices [1;0] gives J(7,8). *)
Example ex_project : join_output_fact (T := nat) [8; 7] concl = Some factJ := eq_refl.

(*==========================================================================*)
(*  Layer 3: the rule fires ([hw_rule_impl] derives J(7,8) from A(7,8),B(8,7)).*)
(*==========================================================================*)

Example J_fires : hw_rule_impl tries hrJ factJ hyps'.
Proof.
  unfold hw_rule_impl. cbn [hrJ hhyps hconcls hsig]. split.
  - (* shape gate: each hypothesis fact matches its (relation, arity) signature *)
    repeat constructor.
  - (* the binding y = 8, x = 7 (ordering is (y,x)) *)
    exists [8; 7]. split.
    + (* query_sat: both joins are satisfied *)
      unfold query_sat. cbn [hhyps length seq combine]. split; [reflexivity |].
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
      * (* join for y (level 0): every entry reads 8 *)
        cbn. exists 8. split; [reflexivity |].
        cbn [joinY HardwareProgram.tries trie_levels clauses zip3].
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn.
        -- exists trieA, [7; 8]. repeat split; reflexivity.   (* A (swapped) reads y = 8 *)
        -- exists trieB, [8; 7]. repeat split; reflexivity.   (* B also reads y = 8 *)
      * (* join for x (level 1): every entry reads 7 *)
        cbn. exists 7. split; [reflexivity |].
        cbn [joinX HardwareProgram.tries trie_levels clauses zip3].
        apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn.
        -- exists trieA, [7; 8]. repeat split; reflexivity.
        -- exists trieB, [8; 7]. repeat split; reflexivity.
    + (* the conclusion projects to J(7,8) *)
      exists concl. split; [left; reflexivity | reflexivity].
Qed.

(*==========================================================================*)
(*  Layer 4: the node derives J(7,8) ([node_run] = proof-tree closure).        *)
(*==========================================================================*)

(* The single rule fires from any fact set that holds A(7,8) and B(8,7) as leaves. *)
Lemma node_run_from (Q : @Datalog.fact rel_id nat -> Prop) :
  Q factA -> Q factB -> node_run tries hp Q factJ.
Proof.
  intros HA HB. eapply pftree_step.
  - (* the single rule [hrJ] fires, producing J(7,8) ... *)
    apply Exists_cons_hd. exact J_fires.
  - (* ... and its two hypotheses are leaves of [Q]. *)
    apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
    + apply pftree_leaf. exact HA.
    + apply pftree_leaf. exact HB.
Qed.

(* The base facts delivered to this node. *)
Definition inputs : @Datalog.fact rel_id nat -> Prop := fun f => f = factA \/ f = factB.

Example J_in_node_run : node_run tries hp inputs factJ.
Proof. apply node_run_from; [left | right]; reflexivity. Qed.

(* The capstone of the node story: the program the COMPILER GENERATED, run on the node,
   derives J(7,8). *)
Example J_derived_by_compiled : node_run gen_tries gen_prog inputs factJ.
Proof. rewrite tries_generated, rule_generated. exact J_in_node_run. Qed.

(*==========================================================================*)
(*  Layer 5: a DISTRIBUTED run of the compiled network                        *)
(*  ([DistributedHardwareSemantics.run_ninfos]).                              *)
(*==========================================================================*)

(* The compiler's whole output -- here a one-element [ninfos] for node (0,0). *)
Definition ninfos : list (@node_info node_id _) :=
  match jcompiled with Result.Success l => l | _ => [] end.

Definition node00 : node_id := [0; 0]%nat.

(* The runtime EDB: deliver A(7,8) and B(8,7) at node (0,0).  The output sink: node (0,0)
   answers for J (relation id 0). *)
Definition dinput : node_id -> @Datalog.fact rel_id nat -> Prop :=
  fun n f => n = node00 /\ (f = factA \/ f = factB).
Definition doutput : node_id -> rel_id -> Prop :=
  fun n r => n = node00 /\ r = 0.

(* The distributed operational semantics, run on the compiled [ninfos], parks J(7,8) at the
   output node.  Steps: deliver A, deliver B, then the node runs its hardware program. *)
Example J_run_distributed :
  @run_ninfos nat node_id _ _
             ninfos dinput doutput factJ.
Proof.
  (* the compiled node's tries / trie-join program are exactly our literals *)
  assert (HTr : @node_tries node_id _ _
                  ninfos node00 = tries) by (vm_compute; reflexivity).
  assert (HP  : @node_prog  node_id _ _
                  ninfos node00 = hp)    by (vm_compute; reflexivity).
  unfold run_ninfos, hw_run_output.
  (* the answer lives at node (0,0), in the config reached after delivering A,B and running *)
  exists node00, node00,
    (cadd (cadd (cadd (fun _ _ _ => False) node00 node00 factA) node00 node00 factB)
       node00 node00 factJ).
  split; [| split].
  - (* reachable: deliver A, deliver B, then run the node's program *)
    eapply dreachS; [eapply dreachS; [eapply dreachS; [apply dreach0 |] |] |].
    + apply dstep_input. split; [reflexivity | left;  reflexivity].
    + apply dstep_input. split; [reflexivity | right; reflexivity].
    + (* the node fires its one rule on the A,B it now holds *)
      eapply dstep_run with (hyps := [factA; factB]).
      * rewrite HTr, HP. apply Exists_cons_hd. exact J_fires.
      * apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
        -- (* A(7,8) is present *)
           exists node00. unfold cadd. left; right; repeat split; reflexivity.
        -- (* B(8,7) is present *)
           exists node00. unfold cadd. right; repeat split; reflexivity.
  - (* J(7,8) is present at node (0,0) *) unfold cadd. right; repeat split; reflexivity.
  - (* node (0,0) is the output sink for J (relation 2) *) split; reflexivity.
Qed.
