From Stdlib Require Import List Bool Relation_Operators.
From Datalog Require Import Datalog.
From Datalog.Util Require Import Pftree.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.
From DatalogRocq Require Import Topologies.Graph.

Import ListNotations.

Section DistributedDatalog.

  Context `{params : datalog_params}.
  Context {Node : Type}.

  (* An atom in a rule is a [clause]; a rule is the [rule.impl | rule.agg] inductive
     (meta-rules live separately, in [program.meta_rules]); a ground/runtime fact is a
     [fact] ([fact.normal nf] or [fact.meta mf]). *)

  Definition ForwardingTable := rel -> list Node.
  Definition ForwardingFn := Node -> ForwardingTable.
  Definition InputFn := Node -> fact -> Prop.
  Definition OutputFn := Node -> rel -> Prop.
  Definition Layout := Node -> list rule.

  Record DataflowNetwork := {
    graph : Graph (Node := Node);
    forward : ForwardingFn;
    input :  InputFn;
    output : OutputFn;
    layout : Layout
  }.

Inductive network_prop :=
  | FactOnNode (n : Node) (f : fact)
  | Output (n : Node) (f : fact).

Fixpoint get_facts_on_node (nps : list (network_prop)) : list (Node * fact) :=
  match nps with
  | [] => []
  | FactOnNode n f :: t => (n, f) :: get_facts_on_node t
  | Output n f :: t => get_facts_on_node t
  end.

Inductive network_step (net : DataflowNetwork) : network_prop -> list (network_prop) -> Prop :=
  | Input n f :
      net.(input) n f ->
      network_step net (FactOnNode n f) []
  | RuleApp n nf r hyps :
      In r (net.(layout) n) ->
      Forall (fun n' => n' = n) (map fst (get_facts_on_node hyps)) ->
      rule.interp r nf (map snd (get_facts_on_node hyps)) ->
      network_step net (FactOnNode n (fact.normal nf)) (hyps)
  | Forward n n' f :
      In n' (net.(forward) n (fact.rel f)) ->
      network_step net (FactOnNode n' f) [FactOnNode n f]
  | OutputStep n f :
      net.(output) n (fact.rel f) ->
      network_step net (Output n f) [FactOnNode n f].

Definition network_pftree (net : DataflowNetwork) : network_prop -> Prop :=
  pftree (fun fact_node hyps => network_step net fact_node hyps) (fun _ => False).

Definition network_prog_impl_fact (net : DataflowNetwork) : fact -> Prop :=
  fun f => exists n, network_pftree net (Output n f).

(* A good layout has every program rule on a node somewhere AND only assigns rules from
   the program to nodes *)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ In r (layout n)) program /\
   forall n r, (In r (layout n) -> nodes n /\ In r program).

(* n produces facts of relation [rel] -- some rule on n has [rel] among its conclusion
   relations ([rule.concl_rels] handles impl/agg uniformly). *)
Definition node_produces (layout : Layout) (n : Node) (r : rel) : Prop :=
  exists rule, In rule (layout n) /\ In r (rule.concl_rels rule).

(* n consumes facts of relation [rel] -- some rule on n has [rel] among its hypothesis
   relations ([rule.hyp_rels] handles impl/agg uniformly). *)
Definition node_consumes (layout : Layout) (n : Node) (r : rel) : Prop :=
  exists rule, In rule (layout n) /\ In r (rule.hyp_rels rule).

(* n1 forwards facts of relation r directly to n2 *)
Definition forwards_rel (forward : ForwardingFn) (r : rel) (n1 n2 : Node) : Prop :=
  In n2 (forward n1 r).

(* n2 is reachable from n1 via forwarding for relation r in zero or more steps *)
Definition forwarding_reachable (forward : ForwardingFn) (r : rel) :=
  clos_refl_trans_1n _ (forwards_rel forward r).

(* A walk whose every consecutive pair forwards [r] makes its last node forwarding-reachable
   from its first.  This is the bridge from a laid-down forwarding path to
   the [forwarding_reachable] closure that [good_source] reasons about. *)
Lemma forwarding_chain_reachable (forward : ForwardingFn) (r : rel) :
  forall (path : list Node) (a b : Node),
  (forall i x y, nth_error path i = Some x -> nth_error path (S i) = Some y -> In y (forward x r)) ->
  nth_error path 0 = Some a ->
  nth_error path (pred (length path)) = Some b ->
  forwarding_reachable forward r a b.
Proof.
  induction path as [|x [|y rest] IH]; intros a b Hcons Ha Hb.
  - discriminate Ha.
  - cbn in Ha, Hb. injection Ha as <-. injection Hb as <-. apply rt1n_refl.
  - cbn in Ha. injection Ha as <-.
    assert (Hxy : In y (forward x r)) by (apply (Hcons 0 x y); reflexivity).
    assert (Hcons' : forall i u v, nth_error (y :: rest) i = Some u ->
                       nth_error (y :: rest) (S i) = Some v -> In v (forward u r)).
    { intros i u v Hu Hv. apply (Hcons (S i) u v); cbn; [exact Hu | exact Hv]. }
    assert (Hb' : nth_error (y :: rest) (pred (length (y :: rest))) = Some b)
      by (cbn [length pred] in Hb |- *; cbn [nth_error] in Hb; exact Hb).
    exact (rt1n_trans _ _ _ _ _ Hxy (IH y b Hcons' eq_refl Hb')).
Qed.

(* The forwarding table is good for a relation r if for every producer,
   there is a path to every consumer *)
Definition good_forwarding_prod_cons (net : DataflowNetwork) (r : rel) : Prop :=
  forall n_prod n_cons,
    node_produces net.(layout) n_prod r ->
    node_consumes net.(layout) n_cons r ->
    forwarding_reachable net.(forward) r n_prod n_cons.

Definition good_forwarding_output_nodes (net : DataflowNetwork) (r : rel) : Prop :=
  forall n_prod,
    node_produces (layout net) n_prod r ->
    exists n_out,
      output net n_out r /\ forwarding_reachable (forward net) r n_prod n_out.

(* Apply it to all relations *)
Definition good_forwarding_complete (net : DataflowNetwork) : Prop :=
  forall rel, good_forwarding_prod_cons net rel /\ good_forwarding_output_nodes net rel.

(* A good forwarding function should only be able to forward things along the
   edges *)
Definition good_forwarding_sound (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 r, In n2 (forward n1 r) -> nodes n1 /\ nodes n2 /\ edges n1 n2.

Definition good_forwarding (forward : ForwardingFn) (net : DataflowNetwork): Prop :=
  good_forwarding_sound forward net.(graph).(nodes) net.(graph).(edge) /\
  good_forwarding_complete net.

Definition good_input (input : InputFn) (program : list rule) : Prop :=
  forall n f, input n f ->
    program.interp_step {| program.rules := program; program.meta_rules := [] |} f [].

Definition good_output (net : DataflowNetwork) : Prop :=
  forall (n : Node) (f : fact),
    node_produces (layout net) n (fact.rel f) ->
    exists n_out, net.(graph).(nodes) n_out /\ net.(output) n_out (fact.rel f).

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net /\
  good_input net.(input) program /\
  good_output net.

(*============================================================================*)
(*  Streaming model: base facts [Q] injected at per-relation input nodes      *)
(*============================================================================*)

(* A node [n] is a *good source* for relation [R] when a fact of relation [R] sitting at [n]
   reaches (by forwarding, or is already at) every consumer of [R] and some output node.  Both
   producers (by [good_forwarding]) and input nodes (by [good_input_streaming]) are good sources;
   this is the single property soundness/completeness reason about. *)
(* A node [n] is a good source for [R] when a fact of [R] at [n] reaches every consumer of [R], and --
   *when [R] is a declared output relation* (some node outputs it) -- also reaches an output node.
   Internal relations (no output node) are not required to reach any output; the top-level
   equivalence is correspondingly stated only for declared-output relations. *)
Definition good_source (net : DataflowNetwork) (n : Node) (R : rel) : Prop :=
  (forall n_cons, node_consumes net.(layout) n_cons R ->
     forwarding_reachable net.(forward) R n n_cons) /\
  ((exists n_out, net.(output) n_out R) ->
   exists n_out, net.(output) n_out R /\ forwarding_reachable net.(forward) R n n_out).

(* Streaming input: the network's input facts are *exactly* the base facts [Q], and each base
   fact is injected at an input node that is a good source for its relation (so it forwards to
   every consumer and to an output node -- the "per-relation input node + forwarding"). *)
Definition good_input_streaming (net : DataflowNetwork) (Q : fact -> Prop) : Prop :=
  (forall n f, net.(input) n f -> Q f) /\
  (forall f, Q f -> exists n, net.(input) n f /\ good_source net n (fact.rel f)).

(* The streaming well-formedness side condition: graph / layout / forwarding-soundness as before,
   every producer is a good source (forwarding completeness, bundling prod->cons and prod->output),
   and the input is the streaming distribution of [Q]. *)
Definition good_network_streaming (net : DataflowNetwork) (program : list rule) (Q : fact -> Prop) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding_sound net.(forward) net.(graph).(nodes) net.(graph).(edge) /\
  (forall n_prod R, node_produces net.(layout) n_prod R -> good_source net n_prod R) /\
  good_input_streaming net Q.

Lemma get_facts_on_node_in (l : list network_prop) (n : Node) (g : fact) :
  In (n, g) (get_facts_on_node l) -> In (FactOnNode n g) l.
Proof.
  induction l as [| p l IH]; cbn; [intros []|].
  destruct p as [n0 g0 | n0 g0].
  - intros [Heq | Hin]; [injection Heq as -> ->; left; reflexivity | right; apply IH, Hin].
  - intros Hin; right; apply IH, Hin.
Qed.

Lemma facts_on_node_map_fst (n : Node) (l : list fact) :
  Forall (fun n' => n' = n) (map fst (get_facts_on_node (map (FactOnNode n) l))).
Proof. induction l as [|a l IH]; cbn; [constructor | constructor; [reflexivity | exact IH]]. Qed.

Lemma facts_on_node_map_snd (n : Node) (l : list fact) :
  map snd (get_facts_on_node (map (FactOnNode n) l)) = l.
Proof. induction l as [|a l IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(* [pftree] induction predicate for the network: every derivable network proposition's
   carried fact is derivable from the program given the base facts [Q]. *)
Definition np_sound (p : list rule) (Q : fact -> Prop) (np : network_prop) : Prop :=
  match np with
  | FactOnNode _ f => program.interp {| program.rules := p; program.meta_rules := [] |} Q f
  | Output _ f => program.interp {| program.rules := p; program.meta_rules := [] |} Q f
  end.

Theorem soundness'' (net : DataflowNetwork) (p : list rule) (Q : fact -> Prop) :
  (forall n f, net.(input) n f -> Q f) ->
  good_layout net.(layout) net.(graph).(nodes) p ->
  forall np, network_pftree net np -> np_sound p Q np.
Proof.
  intros HinQ [Hlc Hls]. unfold network_pftree.
  apply (pftree.ind (fun fact_node hyps => network_step net fact_node hyps)
           (fun _ => False) (np_sound p Q)).
  - intros x [].
  - intros np l Hstep _ IH. inversion Hstep; subst; simpl in *.
    + (* Input: an input fact is a base fact [Q], hence a pftree leaf *)
      match goal with Hin : net.(input) ?n ?f |- _ =>
        apply pftree.leaf; exact (HinQ n f Hin) end.
    + (* RuleApp: fire r at n, hyps already sound by IH *)
      match goal with Hl : In ?r (net.(layout) ?n) |- _ =>
        destruct (Hls n r Hl) as [Hnode Hrin] end.
      eapply pftree.step with (l := map snd (get_facts_on_node l)).
      * constructor. apply Exists_exists. exists r. split; [exact Hrin |
          match goal with Hr : rule.interp r _ _ |- _ => exact Hr end].
      * (* every hyp fact is program-derivable, from IH on the FactOnNode premises *)
        apply Forall_forall. intros f' Hf'in.
        apply in_map_iff in Hf'in. destruct Hf'in as [[n' f''] [Heq Hin]]. simpl in Heq. subst f''.
        (* the (n', f') comes from a FactOnNode n' f' premise in l *)
        rewrite Forall_forall in IH.
        assert (Hnp : In (FactOnNode n' f') l).
        { clear -Hin. induction l as [|a l IHl]; simpl in *; [contradiction|].
          destruct a; simpl in Hin.
          - destruct Hin as [Heq | Hin]; [inversion Heq; subst; left; reflexivity | right; auto].
          - right; auto. }
        specialize (IH _ Hnp). simpl in IH. exact IH.
    + (* Forward: same fact, carried over *)
      rewrite Forall_forall in IH.
      specialize (IH (FactOnNode n f)). simpl in IH. apply IH. left. reflexivity.
    + (* OutputStep: same fact, carried over *)
      rewrite Forall_forall in IH.
      specialize (IH (FactOnNode n f)). simpl in IH. apply IH. left. reflexivity.
Qed.

Theorem soundness (net : DataflowNetwork) (p : list rule) (Q : fact -> Prop) :
  forall f,
  (forall n f, net.(input) n f -> Q f) ->
  good_layout net.(layout) net.(graph).(nodes) p ->
  network_prog_impl_fact net f ->
  program.interp {| program.rules := p; program.meta_rules := [] |} Q f.
Proof.
  intros f HinQ Hgl [n Hpf].
  apply (soundness'' net p Q HinQ Hgl (Output n f) Hpf).
Qed.

Lemma forwarding_lifts :
  forall net n1 n2 f,
    network_pftree net (FactOnNode n1 f) ->
    forwarding_reachable net.(forward) (fact.rel f) n1 n2 ->
    network_pftree net (FactOnNode n2 f).
Proof.
  intros net n1 n2 f Hpf Hreach. revert Hpf.
  induction Hreach as [|x y z Hxy _ IH]; intros Hpf; [exact Hpf|].
  apply IH. eapply pftree.step with (l := [FactOnNode x f]).
  + apply Forward. exact Hxy.
  + constructor; [exact Hpf | constructor].
Qed.

(* If rule [r] at node [n] derives [nf], then [n] is a producer of [nf]'s relation. *)
Lemma interp_node_produces :
  forall (r : rule) (nf : normal_fact) (hyps : list fact) (n : Node) (net : DataflowNetwork),
    rule.interp r nf hyps ->
    In r (layout net n) ->
    node_produces (layout net) n nf.(normal_fact.rel).
Proof.
  intros r nf hyps n net Hr Hin_layout.
  exists r. split; [exact Hin_layout | exact (rule.interp_concl_relname_in _ _ _ Hr)].
Qed.

(* If rule [r] at node [n] consumes [f'], then [n] is a consumer of [f']'s relation. *)
Lemma interp_node_consumes :
  forall (r : rule) (nf : normal_fact) (hyps : list fact) (f' : fact) (n : Node) (net : DataflowNetwork),
    rule.interp r nf hyps ->
    In f' hyps ->
    In r (layout net n) ->
    node_consumes (layout net) n (fact.rel f').
Proof.
  intros r nf hyps f' n net Hr Hf'in Hin_layout.
  exists r. split; [exact Hin_layout |].
  apply rule.interp_hyp_relname_in in Hr. rewrite Forall_forall in Hr. auto.
Qed.

(* If a fact is at a producer, it can be forwarded to any consumer *)
(* A fact at a good source for its relation can be carried to any consumer of that relation. *)
Lemma fact_at_source_consumer :
  forall (net : DataflowNetwork) (f : fact) (n n_cons : Node),
    network_pftree net (FactOnNode n f) ->
    good_source net n (fact.rel f) ->
    node_consumes (layout net) n_cons (fact.rel f) ->
    network_pftree net (FactOnNode n_cons f).
Proof.
  intros net f n n_cons Hpf [Hcons _] Hc.
  eapply forwarding_lifts; [exact Hpf | exact (Hcons n_cons Hc)].
Qed.

(* Every derivable fact (from base facts [Q]) exists at a node that is a good source for its
   relation -- a producer for a derived fact, or the input node for a base fact. *)
Lemma completeness_with_source (net : DataflowNetwork) (p : list rule) (Q : fact -> Prop) :
  good_network_streaming net p Q ->
  forall f, program.interp {| program.rules := p; program.meta_rules := [] |} Q f ->
    exists n, network_pftree net (FactOnNode n f) /\ good_source net n (fact.rel f).
Proof.
  intros Hnet.
  destruct Hnet as [Hgraph [[Hlc Hls] [Hfwds [Hprodsrc [HinQ_s HinQ_c]]]]].
  rewrite Forall_forall in Hlc.
  apply (pftree.ind
           (program.interp_step {| program.rules := p; program.meta_rules := [] |})
           Q
           (fun f => exists n, network_pftree net (FactOnNode n f) /\
                               good_source net n (fact.rel f))).
  - (* leaf: a base fact is injected at its input node, which is a good source *)
    intros f HQ. destruct (HinQ_c f HQ) as [n [Hin Hsrc]].
    exists n. split; [|exact Hsrc].
    eapply pftree.step with (l := []); [apply Input; exact Hin | constructor].
  - (* step: a rule fires; the producing node is a good source *)
    intros f l Hstep _ IH.
    destruct Hstep as [nf l Hexists | mf mhyps Hexists]; [|inversion Hexists].
    apply Exists_exists in Hexists. destruct Hexists as [r [Hr_in Hr]].
    destruct (Hlc r Hr_in) as [n_r [Hn_r_node Hn_r_layout]].
    assert (Hprod : node_produces (layout net) n_r nf.(normal_fact.rel))
      by (eapply interp_node_produces; eauto).
    assert (Hsrc : good_source net n_r nf.(normal_fact.rel)) by (apply Hprodsrc; exact Hprod).
    exists n_r. split; [|exact Hsrc].
    (* every hypothesis is available at [n_r] (forwarded from its own source to this consumer) *)
    assert (Hlifted : Forall (fun f' => network_pftree net (FactOnNode n_r f')) l).
    { rewrite Forall_forall in IH |- *. intros f' Hf'in.
      destruct (IH f' Hf'in) as [n' [Hpf' Hsrc']].
      assert (Hcons : node_consumes (layout net) n_r (fact.rel f'))
        by (eapply interp_node_consumes; eauto).
      eapply fact_at_source_consumer; eauto. }
    eapply pftree.step with (l := List.map (FactOnNode n_r) l).
    + apply RuleApp with (r := r).
      * exact Hn_r_layout.
      * apply facts_on_node_map_fst.
      * rewrite facts_on_node_map_snd. exact Hr.
    + apply Forall_map.
      rewrite Forall_forall in Hlifted |- *. intros f' Hf'in. apply Hlifted. exact Hf'in.
Qed.

Theorem completeness (net : DataflowNetwork) (p : list rule) (Q : fact -> Prop) :
  good_network_streaming net p Q ->
  forall f, program.interp {| program.rules := p; program.meta_rules := [] |} Q f ->
    (exists n_out, net.(output) n_out (fact.rel f)) ->
    network_prog_impl_fact net f.
Proof.
  intros Hnet f Hprog Houtrel.
  destruct (completeness_with_source net p Q Hnet f Hprog) as [n [Hpf Hsrc]].
  destruct Hsrc as [_ Hout2]. destruct (Hout2 Houtrel) as [n_out [Hout Hreach]].
  exists n_out.
  eapply pftree.step with (l := [FactOnNode n_out f]).
  - apply OutputStep. exact Hout.
  - constructor; [| constructor].
    eapply forwarding_lifts; [exact Hpf | exact Hreach].
Qed.

End DistributedDatalog.
