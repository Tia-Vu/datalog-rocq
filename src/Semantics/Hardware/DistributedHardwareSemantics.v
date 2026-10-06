(* OPERATIONAL distributed hardware semantics: a standalone small-step machine that just RUNS the
   compiled program.  Each step either delivers an EDB fact at an input node, fires one of a node's
   hardware rules on facts it currently holds, or forwards a fact to a neighbour per that node's
   forwarding table.  [run_ninfos] runs the compiler's returned [ninfos] directly.

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
From DatalogRocq Require Import Topologies.Graph HardwareProgram DistributedHardwareProgram NodeHardwareSemantics.

Import ListNotations.

Section DistributedHardwareSemantics.

(* Relations are numeric ids at this layer; functions, variables, and values are abstract. *)
Context `{params : datalog_params (_rel := rel_id)}.
Context {node_id : node_idT}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

(* ground/runtime facts at this (numeric-id) layer *)
Abbreviation dl_fact := (Datalog.fact (_rel := rel_id)).

(*============================================================================*)
(*  OPERATIONAL hardware semantics: a standalone small-step machine that just  *)
(*  RUNS the compiled program -- deliver EDB facts, run each node's hardware   *)
(*  program on what it holds, forward facts along the forwarding table.  Built  *)
(*  ONLY from the compiled data (per-node program/tries/forwarding) + the       *)
(*  runtime EDB/sinks -- NO [DistributedDatalog], no graph, no datalog layout.  *)
(*  Its equivalence to the declarative semantics above is a PROVED theorem.     *)
(*============================================================================*)

(* a configuration: which facts are currently present at which node. *)
Definition config := node_id -> dl_fact -> Prop.
Definition cadd (c : config) (n : node_id) (f : dl_fact) : config :=
  fun n0 f0 => c n0 f0 \/ (n0 = n /\ f0 = f).

Section Run.
Context (prog : node_id -> hardware_program) (tries : node_id -> list trie)
        (forward : node_id -> rel_id -> list node_id)
        (input : node_id -> dl_fact -> Prop) (output : node_id -> rel_id -> Prop).

(* one operational step: an EDB fact ENTERS at an input node; a node FIRES one hardware rule on
   facts it currently holds; or a fact is FORWARDED to a neighbour per that node's forwarding
   table. *)
Inductive dstep (c : config) : config -> Prop :=
| dstep_input n f :
    input n f -> dstep c (cadd c n f)
| dstep_run n nf hyps :
    Exists (fun hr => hw_rule_impl (tries n) hr nf hyps) (prog n) ->
    Forall (c n) hyps ->
    dstep c (cadd c n (fact.normal nf))
| dstep_forward n n' f :
    c n f -> In n' (forward n (fact.rel f)) -> dstep c (cadd c n' f).

(* configurations reachable from the empty configuration by stepping. *)
Inductive dreach : config -> Prop :=
| dreach0 : dreach (fun _ _ => False)
| dreachS c c' : dreach c -> dstep c c' -> dreach c'.

(* a fact is PRODUCED by the run when some reachable configuration holds it at an output node. *)
Definition hw_run_output (f : dl_fact) : Prop :=
  exists n c, dreach c /\ c n f /\ output n (fact.rel f).

End Run.

(*----Running the compiler's output [ninfos] directly----*)

Context {forwarding_table : map.map rel_id (list destination)}.

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

(* the forwarding function read off [ninfos]: the EDGE destinations a node lists for a relation. *)
Definition forward_from_ninfos (ninfos : list node_info) (n : node_id) (r : rel_id) : list node_id :=
  flat_map (fun d => match d with
                     | DistributedHardwareProgram.DestEdge n' => [n']
                     | DistributedHardwareProgram.DestTrie _ => [] end)
           (match map.get (find_ninfo ninfos n).(DistributedHardwareProgram.nforwarding) r with
            | Some ds => ds | None => [] end).

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
        (forward : node_id -> rel_id -> list node_id)
        (input : node_id -> dl_fact -> Prop) (output : node_id -> rel_id -> Prop).

Abbreviation step  := (dstep prog tries forward input).
Abbreviation reach := (dreach prog tries forward input).

(* a fact is operationally PRESENT at a node when some reachable config holds it. *)
Definition present (n : node_id) (f : dl_fact) : Prop := exists c, reach c /\ c n f.

(* MONOTONICITY: any step taken from [c] can be replayed from any larger config [d] -- it adds the
   same fact and the result still extends [d].  (This is why processing order is immaterial.) *)
Lemma dstep_replay (c d c' : config) :
  (forall n f, c n f -> d n f) -> step c c' ->
  exists d', step d d' /\ (forall n f, c' n f -> d' n f) /\ (forall n f, d n f -> d' n f).
Proof.
  intros Hsub Hstep. inversion Hstep as [n f Hin | n nf hyps Hfire Hhyps | n n' f Hcnf Hfwd]; subst;
    [ exists (cadd d n f); split; [apply dstep_input; exact Hin |]
    | exists (cadd d n (fact.normal nf)); split;
        [eapply dstep_run; [exact Hfire | exact (Forall_impl _ (Hsub n) Hhyps)] |]
    | exists (cadd d n' f); split;
        [apply (dstep_forward prog tries forward input d n n' f (Hsub n f Hcnf) Hfwd) |] ];
    (split; intros n0 f0; unfold cadd; [intros [H|H]; [left; apply Hsub; exact H | right; exact H]
                                       | intros H; left; exact H]).
Qed.

(* DIRECTEDNESS: any two reachable configs have a common reachable extension.  This is the precise
   sense in which the order facts are processed in does not matter -- two runs can always be merged. *)
Lemma dreach_merge (c1 c2 : config) :
  reach c1 -> reach c2 ->
  exists c, reach c /\ (forall n f, c1 n f -> c n f) /\ (forall n f, c2 n f -> c n f).
Proof.
  intros H1 H2. revert c1 H1. induction H2 as [| c2' c2'' Hr2 IH Hstep2]; intros c1 H1.
  - exists c1. split; [exact H1 | split; [auto | intros n f []]].
  - destruct (IH c1 H1) as [c [Hrc [Hc1 Hc2']]].
    destruct (dstep_replay c2' c c2'' Hc2' Hstep2) as [d [Hstepd [Hc2'' Hcd]]].
    exists d. split; [eapply dreachS; eassumption | split].
    + intros n f Hf. apply Hcd, Hc1, Hf.
    + intros n f Hf. apply Hc2'', Hf.
Qed.

(* Merge a list of separately-present facts (all at node [n]) into ONE reachable config holding them all. *)
Lemma present_list (n : node_id) (hs : list dl_fact) :
  Forall (fun h => present n h) hs -> exists c, reach c /\ Forall (fun h => c n h) hs.
Proof.
  induction hs as [| h hs IH]; intros Hall.
  - exists (fun _ _ => False). split; [apply dreach0 | constructor].
  - pose proof (Forall_inv Hall) as Hh. pose proof (Forall_inv_tail Hall) as Hrest.
    destruct Hh as [ch [Hrch Hchnh]]. destruct (IH Hrest) as [c [Hrc Hcs]].
    destruct (dreach_merge ch c Hrch Hrc) as [d [Hrd [Hchd Hcd]]].
    exists d. split; [exact Hrd | constructor].
    + exact (Hchd n h Hchnh).
    + apply (@Forall_impl _ (fun h => c n h) (fun h => d n h));
        [intros a Ha; exact (Hcd n a Ha) | exact Hcs].
Qed.

End Adequacy.

End DistributedHardwareSemantics.
