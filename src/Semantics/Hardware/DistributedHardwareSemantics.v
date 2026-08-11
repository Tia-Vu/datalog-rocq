(* OPERATIONAL distributed hardware semantics: a standalone small-step machine that just RUNS the
   compiled program.  Each step either delivers an EDB fact at an input node, runs a node's hardware
   program over the facts it currently holds ([NodeHardwareSemantics.node_run]), or forwards a fact
   to a neighbour per that node's forwarding table.  [run_ninfos] runs the compiler's returned
   [ninfos] directly.

   This file deliberately does NOT depend on [DistributedDatalog]: the operational semantics is
   defined purely from the compiled data (per-node program / tries / forwarding) plus the runtime
   EDB and output sinks -- no graph, no datalog layout, no reference network.  The equivalence to
   the declarative [DistributedDatalog]-based semantics (and through it to [Datalog]) is a PROVED
   theorem, isolated in [HardwareDatalogBridge] (the only file that touches [DistributedDatalog]).

   What lives here: [config]/[cadd], [dstep]/[dreach]/[hw_run_output], [find_ninfo]/[run_ninfos],
   and the order-independence machinery ([dstep_replay], [dreach_merge], [present_list]) the bridge
   uses to prove adequacy. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List Bool ZArith.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.
From DatalogRocq Require Import HardwareProgram DistributedHardwareProgram NodeHardwareSemantics.

Import ListNotations.

Section DistributedHardwareSemantics.

(* Relations are numeric ids at this layer; functions, variables, and values are abstract. *)
Context {var : exprvarT} {fn : fnT} {aggregator : aggregatorT} {T : valueT}.
Context `{sig : signature fn aggregator T}.
Context {context : map.map var T} {context_ok : map.ok context}.
Context {node_id : Type}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

(* ground/runtime facts at this (numeric-id) layer *)
Notation dl_fact := (@Datalog.fact rel_id T).

(*============================================================================*)
(*  OPERATIONAL hardware semantics: a standalone small-step machine that just  *)
(*  RUNS the compiled program -- deliver EDB facts, run each node's hardware   *)
(*  program on what it holds, forward facts along the forwarding table.  Built  *)
(*  ONLY from the compiled data (per-node program/tries/forwarding) + the       *)
(*  runtime EDB/sinks -- NO [DistributedDatalog], no graph, no datalog layout.  *)
(*  Its equivalence to the declarative semantics above is a PROVED theorem.     *)
(*============================================================================*)

(* a configuration: which facts are currently present at which node. *)
Definition config := node_id -> node_id -> dl_fact -> Prop.
Definition cadd (c : config) (n s : node_id) (f : dl_fact) : config :=
  fun n0 s0 f0 => c n0 s0 f0 \/ (n0 = n /\ s0 = s /\ f0 = f).

Definition facts_at (c : config) (n : node_id) : dl_fact -> Prop :=
  fun f => exists s, c n s f.

Section Run.
Context (prog : node_id -> hardware_program) (tries : node_id -> list trie)
        (forward : node_id -> rel_id -> node_id -> list node_id)
        (input : node_id -> dl_fact -> Prop) (output : node_id -> rel_id -> Prop).

(* one operational step: an EDB fact ENTERS at an input node; a node FIRES one hardware rule on
   facts it currently holds; or a fact is FORWARDED to a neighbour per that node's forwarding
   table. *)
Inductive dstep (c : config) : config -> Prop :=
| dstep_input n f :
    input n f -> dstep c (cadd c n n f)
| dstep_run n f hyps :
    Exists (fun hr => hw_rule_impl (tries n) hr f hyps) (prog n) ->
    Forall (facts_at c n) hyps ->
    dstep c (cadd c n n f)
| dstep_forward n n' s f :
    c n s f -> In n' (forward n (Datalog.rel_of f) s) -> dstep c (cadd c n' s f).

(* configurations reachable from the empty configuration by stepping. *)
Inductive dreach : config -> Prop :=
| dreach0 : dreach (fun _ _ _ => False)
| dreachS c c' : dreach c -> dstep c c' -> dreach c'.

(* a fact is PRODUCED by the run when some reachable configuration holds it at an output node. *)
Definition hw_run_output (f : dl_fact) : Prop :=
  exists n s c, dreach c /\ c n s f /\ output n (Datalog.rel_of f).

End Run.

(*----Running the compiler's output [ninfos] directly----*)

Context {forwarding_table : map.map (rel_id * node_id) (list node_id)}.
Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

(* read a node's compiled data off the returned [ninfos] (empty default if the node is absent). *)
Definition find_ninfo (ninfos : list node_info) (n : node_id) : node_info :=
  match List.find (fun ni => eqb ni.(DistributedHardwareProgram.nid) n) ninfos with
  | Some ni => ni
  | None => {| DistributedHardwareProgram.nid := n; DistributedHardwareProgram.nprogram := [];
               DistributedHardwareProgram.nforwarding := map.empty; DistributedHardwareProgram.ntries := [] |}
  end.

(* the hardware program / trie read-specs a node runs, read straight off its [node_info]. *)
Definition node_prog (ninfos : list node_info) (n : node_id) : hardware_program :=
  (find_ninfo ninfos n).(DistributedHardwareProgram.nprogram).
Definition node_tries (ninfos : list node_info) (n : node_id) : list trie :=
  (find_ninfo ninfos n).(DistributedHardwareProgram.ntries).

(* the forwarding function read off [ninfos]: the destinations a node lists for a relation. *)
Definition forward_from_ninfos (ninfos : list node_info) (n : node_id) (r : rel_id)
    (original_source : node_id) : list node_id :=
  match map.get (find_ninfo ninfos n).(DistributedHardwareProgram.nforwarding) (r, original_source) with
  | Some ds => ds | None => [] end.

(* RUN THE COMPILED NETWORK, straight from the compiler output [ninfos]: each node runs [node_prog]
   over the facts it holds (reading them through [node_tries]) and forwards along [forward_from_ninfos];
   [input]/[output] are the runtime EDB sources / answer sinks.  [run_ninfos ninfos input output f] is
   the predicate "the run can park fact [f] at an output node" -- the distributed [hw_run_output] with
   every node's data sourced from its [node_info].  NO [DistributedDatalog] anywhere in its definition. *)
Definition run_ninfos (ninfos : list node_info) (input : node_id -> dl_fact -> Prop)
    (output : node_id -> rel_id -> Prop) : dl_fact -> Prop :=
  hw_run_output (node_prog ninfos) (node_tries ninfos) (forward_from_ninfos ninfos) input output.

(*============================================================================*)
(*  ADEQUACY: the operational run [hw_run_output] equals the declarative        *)
(*  [hw_net_prog_impl_fact].  Monotonicity (queue order doesn't matter) is the  *)
(*  engine; everything else is two inductions.                                  *)
(*============================================================================*)

Section Adequacy.
Context (prog : node_id -> hardware_program) (tries : node_id -> list trie)
        (forward : node_id -> rel_id -> node_id -> list node_id)
        (input : node_id -> dl_fact -> Prop) (output : node_id -> rel_id -> Prop).

Notation step  := (dstep prog tries forward input).
Notation reach := (dreach prog tries forward input).

(* a fact is operationally PRESENT at a node when some reachable config holds it. *)
Definition present (n s : node_id) (f : dl_fact) : Prop := exists c, reach c /\ c n s f.

(* MONOTONICITY: any step taken from [c] can be replayed from any larger config [d] -- it adds the
   same fact and the result still extends [d].  (This is why processing order is immaterial.) *)
Lemma dstep_replay (c d c' : config) :
  (forall n s f, c n s f -> d n s f) -> step c c' ->
  exists d', step d d' /\ (forall n s f, c' n s f -> d' n s f)
             /\ (forall n s f, d n s f -> d' n s f).
Proof.
  intros Hsub Hstep. inversion Hstep as [n f Hin | n f hyps Hfire Hhyps | n n' s f Hcnf Hfwd]; subst;
    [ exists (cadd d n n f); split; [apply dstep_input; exact Hin |]
    | exists (cadd d n n f); split;
        [eapply dstep_run;
           [ exact Hfire
           | rewrite Forall_forall in Hhyps |- *; intros h Hh;
             destruct (Hhyps h Hh) as [s0 Hs0]; exists s0; exact (Hsub n s0 h Hs0) ] |]
    | exists (cadd d n' s f); split;
        [apply (dstep_forward prog tries forward input d n n' s f (Hsub n s f Hcnf) Hfwd) |] ];
    (split; intros n0 s0 f0; unfold cadd; [intros [H|H]; [left; apply Hsub; exact H | right; exact H]
                                          | intros H; left; exact H]).
Qed.

(* DIRECTEDNESS: any two reachable configs have a common reachable extension.  This is the precise
   sense in which the order facts are processed in does not matter -- two runs can always be merged. *)
Lemma dreach_merge (c1 c2 : config) :
  reach c1 -> reach c2 ->
  exists c, reach c /\ (forall n s f, c1 n s f -> c n s f) /\ (forall n s f, c2 n s f -> c n s f).
Proof.
  intros H1 H2. revert c1 H1. induction H2 as [| c2' c2'' Hr2 IH Hstep2]; intros c1 H1.
  - exists c1. split; [exact H1 | split; [auto | intros n s f []]].
  - destruct (IH c1 H1) as [c [Hrc [Hc1 Hc2']]].
    destruct (dstep_replay c2' c c2'' Hc2' Hstep2) as [d [Hstepd [Hc2'' Hcd]]].
    exists d. split; [eapply dreachS; eassumption | split].
    + intros n s f Hf. apply Hcd, Hc1, Hf.
    + intros n s f Hf. apply Hc2'', Hf.
Qed.

(* Merge a list of separately-present facts (all at node [n]) into ONE reachable config holding them all. *)
Lemma present_list (n : node_id) (hs : list dl_fact) :
  Forall (fun h => exists s, present n s h) hs ->
  exists c, reach c /\ Forall (fun h => facts_at c n h) hs.
Proof.
  induction hs as [| h hs IH]; intros Hall.
  - exists (fun _ _ _ => False). split; [apply dreach0 | constructor].
  - pose proof (Forall_inv Hall) as Hh. pose proof (Forall_inv_tail Hall) as Hrest.
    destruct Hh as [s [ch [Hrch Hchnh]]]. destruct (IH Hrest) as [c [Hrc Hcs]].
    destruct (dreach_merge ch c Hrch Hrc) as [d [Hrd [Hchd Hcd]]].
    exists d. split; [exact Hrd | constructor].
    + exists s. exact (Hchd n s h Hchnh).
    + apply (@Forall_impl _ (fun h => facts_at c n h) (fun h => facts_at d n h));
        [intros a [s0 Ha]; exists s0; exact (Hcd n s0 a Ha) | exact Hcs].
Qed.

End Adequacy.

End DistributedHardwareSemantics.
