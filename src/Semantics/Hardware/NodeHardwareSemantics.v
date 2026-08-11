(* Here we define the higher level operational semantics of how a trie join works. This is abstracted only
   for a single node, which can be distributed later for the distributed semantics.

   The compiler ([DistributedDatalogToHardwareCompiler]) turns a lowered datalog program (relations
   renamed to numeric ids, functions and variables intact) into a [hardware_program]:
   a list of [hardware_rule]s, each a *trie-join* query.  A query is a sequence of
   [join]s, one per variable in the rule's variable ordering; each join intersects
   a set of tries (stored, column-permuted relations) at a given level.

   This file gives that hardware representation a *declarative* semantics on a single node
   ([hw_prog_impl_fact]) and defines what it means for it to be correct: a node *implements*
   an ordinary [Datalog] program [P] (over the numeric ids the hardware uses) when the two
   derive exactly the same facts ([node_implements]).

       hardware_program  --(hw_prog_impl_fact)-->  facts
              ||  node_implements                     ||
          [Datalog] program P  --(Datalog.prog_impl_fact)-->  facts

   [hw_node_correct] reduces this to a per-rule bridge [hw_rule_matches].  NodeHardwareSemantics is
   compiler-agnostic: it never mentions the compiler's [lowered_rule] AST.  Proving a *compiled*
   hardware program implements its source program is the job of [DistributedDatalogToHardwareCompilerCorrect]; the
   distributed version is [DistributedHardwareSemantics]. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.
From DatalogRocq Require Import HardwareProgram.

Import ListNotations.

Section NodeHardwareSemantics.

(* Relation names are already numeric ([rel_id] = [nat]) at this stage; functions,
   variables, and the value type stay abstract. *)
Context {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context `{sig : signature fn aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {var_eqb : Eqb var} {var_eqb_ok : Eqb_ok var_eqb}.

(* The reference programs this node is verified against are ordinary [Datalog] programs over
   the numeric ids the hardware uses.  NodeHardwareSemantics never mentions the compiler's [lowered_rule]
   AST: the hardware program is compared directly to a [Datalog] program.  (Turning a compiled
   [lowered_rule] into such a [dl_rule], and proving the compiled hardware matches it, is the
   compiler's job in [DistributedDatalogToHardwareCompilerCorrect].) *)
Notation dl_rule := (@Datalog.rule rel_id var fn aggregator).
Notation dl_program := (list dl_rule).
(* Ground/runtime facts are [Datalog.fact]s ([normal_fact R args]); the bare fragment
   never produces [meta_fact]s. *)
Notation dl_fact := (@Datalog.fact rel_id T).

(*============================================================================*)
(*  Trie-join (hardware) semantics on a single node                           *)
(*============================================================================*)

(* A node stores a set of [trie]s; trie [t] is relation [t.(trel)] re-indexed by the
   column permutation [t.(tperm)] : [tperm] sends an *original* argument position [a]
   to the *trie level* (column in storage) it occupies.  Hypothesis facts [hyps']
   below are kept in original column order (exactly datalog facts), so to read the
   value a join wants at [level] we invert [tperm] back to the original position. *)

Definition lookup_trie (tries : list trie) (id : trie_id) : option trie :=
  find (fun t => Nat.eqb t.(tid) id) tries.

(* First position [a] with [nth a perm = level] (the inverse of the permutation). *)
Fixpoint inv_perm_index (perm : permutation) (level : nat) : option nat :=
  match perm with
  | [] => None
  | p :: ps =>
    if Nat.eqb p level then Some 0
    else option_map S (inv_perm_index ps level)
  end.

(* Value the trie with permutation [perm] exposes at [level], given a tuple [tup]
   stored in original column order. *)
Definition trie_read (perm : permutation) (tup : list T) (level : nat) : option T :=
  match inv_perm_index perm level with
  | Some a => nth_error tup a
  | None => None
  end.

(*---- index / permutation machinery ----*)

(* [inv_perm_index] is sound: the index it returns really points at [level]. *)
Lemma inv_perm_index_sound : forall perm level a,
  inv_perm_index perm level = Some a -> nth_error perm a = Some level.
Proof.
  induction perm as [|p ps IH]; simpl; intros level a H.
  - discriminate.
  - destruct (Nat.eqb_spec p level) as [->|Hne].
    + injection H as <-. reflexivity.
    + destruct (inv_perm_index ps level) as [a'|] eqn:E; simpl in H; [|discriminate].
      injection H as <-. simpl. apply IH. exact E.
Qed.

(* On a duplicate-free permutation list, [inv_perm_index] returns the unique index. *)
Lemma inv_perm_index_NoDup : forall perm a level,
  NoDup perm -> nth_error perm a = Some level -> inv_perm_index perm level = Some a.
Proof.
  induction perm as [|p ps IH]; simpl; intros a level Hnd Hnth.
  - destruct a; discriminate.
  - inversion Hnd as [|x l Hpin Hnd' Heq]; subst.
    destruct a as [|a']; simpl in Hnth.
    + injection Hnth as <-. rewrite Nat.eqb_refl. reflexivity.
    + assert (Hin : In level ps) by (eapply nth_error_In; eauto).
      destruct (Nat.eqb_spec p level) as [->|Hne].
      * exfalso. auto.
      * rewrite (IH a' level Hnd' Hnth). reflexivity.
Qed.

(* Reading a [NoDup] trie at the level where original column [a] was placed recovers
   exactly column [a] of the stored tuple.  This is the bridge that makes a join entry
   read off the value of the variable sitting at that column. *)
Lemma trie_read_NoDup : forall perm tup a,
  NoDup perm -> a < length perm ->
  trie_read perm tup (nth a perm 0) = nth_error tup a.
Proof.
  intros perm tup a Hnd Hlt. unfold trie_read.
  erewrite inv_perm_index_NoDup; [reflexivity| exact Hnd |].
  apply nth_error_nth'. exact Hlt.
Qed.

Fixpoint zip3 {A B C : Type} (la : list A) (lb : list B) (lc : list C)
  : list (A * B * C) :=
  match la, lb, lc with
  | a :: la', b :: lb', c :: lc' => (a, b, c) :: zip3 la' lb' lc'
  | _, _, _ => []
  end.

(* One (trie, level, clause) entry of a join is satisfied by value [vi] if clause
   [clause] supplies a hypothesis tuple in the trie's relation that reads to [vi]
   at [level]. *)
Definition join_entry_sat (tries : list trie) (hyps' : list dl_fact)
    (vi : T) (e : trie_id * nat * clause_id) : Prop :=
  let '(tid, level, clause) := e in
  exists t hyp_tup,
    lookup_trie tries tid = Some t /\
    nth_error hyps' clause = Some (Datalog.normal_fact t.(trel) hyp_tup) /\
    trie_read t.(tperm) hyp_tup level = Some vi.

(* The [i]-th join binds variable-order position [i]: every entry must read the same
   value [vi = nth_error vals i]. *)
Definition join_sat (tries : list trie) (hyps' : list dl_fact)
    (vals : list T) (i : nat) (j : join) : Prop :=
  exists vi, nth_error vals i = Some vi /\
    Forall (join_entry_sat tries hyps' vi)
           (zip3 j.(HardwareProgram.tries) j.(trie_levels) j.(clauses)).

(* The whole query: one join per variable, in order. *)
Definition query_sat (tries : list trie) (q : query)
    (vals : list T) (hyps' : list dl_fact) : Prop :=
  length vals = length q /\
  Forall (fun '(i, j) => join_sat tries hyps' vals i j)
         (combine (seq 0 (length q)) q).

(* A conclusion projects the binding [vals] through [output_var_indices]. *)
Definition join_output_fact (vals : list T) (jo : join_output) : option dl_fact :=
  match fold_right (fun idx acc =>
          match acc, nth_error vals idx with
          | Some vs, Some v => Some (v :: vs)
          | _, _ => None
          end) (Some []) jo.(output_var_indices) with
  | Some out => Some (Datalog.normal_fact jo.(output_rel) out)
  | None => None
  end.

(* The single-rule semantics, in the same shape as [Datalog.rule_impl]: hardware rule
   [hr] (with trie table [tries]) produces conclusion fact [f] from hypothesis facts
   [hyps'] (one per clause/hypothesis, in clause order).

   The rule fires only when the hypothesis facts have the shape [hr] expects: one fact per
   clause, each tuple with the clause's arity ([hr.(hsig)]).  This makes the hardware as
   strict as [Datalog.rule_impl] (whose [Forall2] forces exactly this), so that no spurious
   facts are derived from over-long or extra hypothesis facts. *)
Definition hw_rule_impl (tries : list trie) (hr : hardware_rule)
    (f : dl_fact) (hyps' : list dl_fact) : Prop :=
  Forall2 (fun sg fct => match fct with
                         | Datalog.normal_fact R args => R = fst sg /\ length args = snd sg
                         | _ => False
                         end) hr.(hsig) hyps' /\
  exists vals,
    query_sat tries hr.(hhyps) vals hyps' /\
    exists jo, In jo hr.(hconcls) /\ join_output_fact vals jo = Some f.

(* THE SINGLE-NODE RUN: from a set of input/base facts [inputs] delivered to this node, the hardware
   program [hp] (with trie table [tries]) derives more facts -- the proof-tree closure where every
   internal node fires some hardware rule and every leaf is an input fact.  "Run the node's program
   on its inputs."  This is the per-node building block of the distributed operational semantics. *)
Definition node_run (tries : list trie) (hp : hardware_program) (inputs : dl_fact -> Prop)
  : dl_fact -> Prop :=
  pftree (fun f hyps' => Exists (fun hr => hw_rule_impl tries hr f hyps') hp) inputs.

(* The proof-tree closure, mirroring [Datalog.prog_impl] with an empty EDB
   ([Q := fun _ => False]): a fact is hardware-derivable iff it is the root of a
   proof tree whose every node fires some hardware rule.  ([node_run] with no inputs.) *)
Definition hw_prog_impl_fact (tries : list trie) (hp : hardware_program)
  : dl_fact -> Prop :=
  node_run tries hp (fun _ => False).

(*============================================================================*)
(*  Correctness: trie-join semantics vs. datalog semantics                    *)
(*============================================================================*)

(* The single-node correctness notion: a hardware program [hp] (with trie table [tries])
   running on one node *implements* the datalog program [P] when, fact-for-fact, the trie-join
   derives exactly what [P] derives.  [P] is an ordinary [Datalog] program over the numeric ids
   the hardware uses -- no compiler AST involved. *)
Definition node_implements (tries : list trie) (hp : hardware_program) (P : dl_program) : Prop :=
  forall f, hw_prog_impl_fact tries hp f <-> Datalog.prog_impl P (fun _ => False) f.

(* Per-rule bridge: hardware rule [hr] (with trie table [tries]) is *correct* for datalog rule
   [r] when, fact-for-fact, the trie-join produces exactly what [r] produces under derivation
   environment [env].  (For the bare/normal fragment [rule_impl] is [env]-independent, so the
   choice of [env] is immaterial.)  Everything else reduces to this; [DistributedDatalogToHardwareCompilerCorrect]
   discharges it for compiled rules via the trie-join argument. *)
Definition hw_rule_matches (tries : list trie)
    (env : list dl_fact -> rel_id -> list T -> Prop) (r : dl_rule) (hr : hardware_rule) : Prop :=
  forall f hyps', hw_rule_impl tries hr f hyps' <-> rule_impl env r f hyps'.

(* Pointwise, the two one-step relations agree once every rule matches. *)
Lemma matches_step (tries : list trie) (P : dl_program) (hp : hardware_program)
    (env : list dl_fact -> rel_id -> list T -> Prop) f hyps' :
  Forall2 (hw_rule_matches tries env) P hp ->
  (Exists (fun hr => hw_rule_impl tries hr f hyps') hp
   <-> Exists (fun r => rule_impl env r f hyps') P).
Proof.
  intros HF. induction HF as [| r hr P' hp' Hmatch HF IH]; simpl.
  - split; intros HE; inversion HE.
  - rewrite !Exists_cons. rewrite IH, (Hmatch f hyps'). reflexivity.
Qed.

(* MODULAR CORRECTNESS (fully proved): if every hardware rule matches its datalog rule, the
   whole node's trie-join semantics derives exactly the datalog program's facts -- i.e. the
   node implements [P].  The deep work is thus isolated to the per-rule obligation. *)
Theorem hw_node_correct (tries : list trie) (P : dl_program) (hp : hardware_program) :
  Forall2 (hw_rule_matches tries (Datalog.one_step_derives P)) P hp ->
  node_implements tries hp P.
Proof.
  intros HF f. cbv [node_implements hw_prog_impl_fact Datalog.prog_impl].
  split; intros H; eapply pftree_weaken; try exact H; intros x l Hx;
    apply (matches_step tries P hp (Datalog.one_step_derives P) _ _ HF); exact Hx.
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
Compute trie_read (T := nat) [1; 0] [10; 20] 0.   (* Some 20 *)
Compute trie_read (T := nat) [1; 0] [10; 20] 1.   (* Some 10 *)

Compute zip3 [0; 1] [1; 1] [0; 1].

(* Projecting a binding [v0;v1;v2] = [7;8;9] through output indices [2;0] => (R, [9;7]). *)
Compute join_output_fact (T := nat) [7; 8; 9]
  {| output_rel := 5; output_var_indices := [2; 0] |}.
