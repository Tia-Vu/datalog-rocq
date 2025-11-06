From Stdlib Require Import List Bool.
From Datalog Require Import Datalog.
From coqutil Require Import Map.Interface Map.Properties Map.Solver Tactics Tactics.fwd Datatypes.List.

Import ListNotations.

Section DistributedDatalog.

  Context {rel var fn aggregator T : Type}.
  Context `{sig : signature fn aggregator T}.
  Context `{query_sig : query_signature rel}.
  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {Node Info : Type}.
  Context {node_eqb : Node -> Node -> bool}.
  Context {node_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (node_eqb x y)}.

  Definition fact := Datalog.fact rel var fn.
  Definition rule := Datalog.rule rel var fn aggregator.

  Record Graph := {
    nodes : Node -> Prop;
    edge : Node -> Node -> Prop
  }.

  Definition good_graph (g : Graph) := 
   forall n1 n2, edge g n1 n2 -> nodes g n1 /\ nodes g n2.

  Inductive path (g : Graph) : Node -> Node -> Prop :=
    | path_nil n :
        g.(nodes) n ->
        path g n n 
    | path_cons n1 n2 n3 :
        g.(edge) n1 n2 ->
        path g n2 n3 ->
        path g n1 n3.
  
  Definition strongly_connected (g : Graph) : Prop :=
    forall n1 n2, g.(nodes) n1 -> g.(nodes) n2 -> path g n1 n2.

  Definition ForwardingFn := Node -> rel * list T -> option Node.
  Definition InputFn := Node -> rel * list T -> Prop.
  Definition OutputFn := Node -> rel * list T -> Prop.
  Definition Layout := Node -> list rule.

  Record DataflowNetwork := {
    graph : Graph;
    forward : ForwardingFn;
    input :  InputFn;
    output : OutputFn;
    layout : Layout
  }.

Inductive network_prop := 
  | FactOnNode (n : Node) (f : rel * list T)
  | Output (n : Node) (f : rel * list T).

Fixpoint get_facts_on_node (nps : list (network_prop)) : list (Node * (rel * list T)) :=
  match nps with
  | [] => []
  | FactOnNode n f :: t => (n, f) :: get_facts_on_node t
  | Output n f :: t => get_facts_on_node t
  end.

Inductive network_step (net : DataflowNetwork) : network_prop -> list (network_prop) -> Prop :=
  | Input n f : 
      net.(input) n f ->
      network_step net (FactOnNode n f) []
  | RuleApp n f r hyps :
      In r (net.(layout) n) ->
      Forall (fun n' => n' = n) (map fst (get_facts_on_node hyps)) ->
      Datalog.rule_impl r f (map snd (get_facts_on_node hyps)) ->
      network_step net (FactOnNode n f) (hyps)
  | Forward n n' f :
      net.(forward) n f = Some n' ->
      network_step net (FactOnNode n' f) [FactOnNode n f]
  | OutputStep n f :
      net.(output) n f ->
      network_step net (Output n f) [FactOnNode n f].

Definition network_pftree (net : DataflowNetwork) : network_prop -> Prop :=
  pftree (fun fact_node hyps => network_step net fact_node hyps).

Definition network_prog_impl_fact (net : DataflowNetwork) : rel * list T -> Prop :=
  fun f => exists n, network_pftree net (FactOnNode n f).

(* A good layout has every program rule on a node somewhere AND only assigns rules from 
   the program to nodes *)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ In r (layout n)) program /\
   forall n r, nodes n /\ (In r (layout n) -> In r program).

(* A good forwarding function should only be able to forward things along the 
   edges *)
Definition good_forwarding (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 f, forward n1 f = Some n2 -> nodes n1 /\ nodes n2 /\ edges n1 n2.  

(* This is a temporary thing, the format will change once we have a solid streaming
   model. *)

Definition good_input (input : InputFn) (program : list rule) : Prop := 
  forall n f, input n f ->
    exists r, In r program /\
              Datalog.rule_impl r f [].

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net.(graph).(nodes) net.(graph).(edge) /\
  good_input net.(input) program.

Lemma Forall_get_facts_on_node :
  forall (l : list network_prop)
         (P : Node * (rel * list T) -> Prop)
         (Q : network_prop -> Prop),
    (forall n f, Q (FactOnNode n f) -> P (n, f)) ->
    Forall Q l ->
    Forall P (get_facts_on_node l).
Proof.
  induction l; intros; simpl; auto.
  - destruct a; simpl in *; auto.
    + econstructor.
      * apply H. inversion H0. assumption.
      * eapply IHl; inversion H0; eauto.
    + eapply IHl; inversion H0; eauto.
Qed.
 
(* Some of these aren't properly formulated with the right conditions yet, but
   this is kinda the framework I'm going for here. *)
Theorem soundness' (net : DataflowNetwork) (program : list rule) :
  forall n f, 
  good_network net program ->
  network_pftree net (FactOnNode n f)  ->
  Datalog.prog_impl_fact program f.
Proof.
  intros. remember (FactOnNode n f) as node_fact.
  generalize dependent n. generalize dependent f.
  induction H0.
  intros.
  subst.
  unfold prog_impl_fact.
  inversion H0.
  - unfold good_network in H. fwd.
    unfold good_input in Hp3.
    specialize (Hp3 n f); subst.
    apply Hp3 in H6.
    econstructor; eauto.
    apply Exists_exists.
    eauto.
  - econstructor.
   + unfold good_network in H. fwd.
     unfold good_layout in Hp1. fwd.
     specialize (Hp1p1 n r). 
     destruct Hp1p1 as [Hnode Hin].
     apply Hin in H5.
     apply Exists_exists.
     exists r; eauto.
   + apply Forall_map; subst.
    eapply Forall_get_facts_on_node; eauto.
    intros.
    simpl in H3.
    eapply H3; eauto.
  - rewrite <- H4 in H2. 
    inversion H2.
    eapply H9; eauto.
Qed.

Theorem soundness (net : DataflowNetwork) (program : list rule) :
  forall f, 
  good_network net program ->
  network_prog_impl_fact net f ->
  Datalog.prog_impl_fact program f.
Proof.
  intros.
  destruct H0.
  unfold network_prog_impl_fact in H0.
  eapply soundness'; eauto.
Qed.

Theorem completeness (net : DataflowNetwork) (program : list rule) :
  forall f, Datalog.prog_impl_fact program f -> 
  good_network net program ->
  network_prog_impl_fact net f.
Proof.
Admitted.

End DistributedDatalog.