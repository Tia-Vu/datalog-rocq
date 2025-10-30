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
  Definition Layout := Node -> list rule.

  Record DataflowNetwork := {
    graph : Graph;
    forward : ForwardingFn;
    layout : Layout
  }.

(* Is there a nicer way to represent this? Seems a bit handwavy or whatever...*)

Inductive network_pftree (net : DataflowNetwork) : Node -> rel * list T -> Prop :=
  | RuleApp n f r hyps :
      In r (net.(layout) n) ->
      Forall (network_pftree net n) hyps ->
      Datalog.rule_impl r f hyps ->
      network_pftree net n f
  | Forward n n' f :
      network_pftree net n f ->
      net.(forward) n f = Some n' ->
      network_pftree net n' f.

Definition network_prog_impl_fact (net : DataflowNetwork) : rel * list T -> Prop :=
  fun f => exists n, network_pftree net n f.
    
Definition rule_assigned_to_node (layout : Layout) (r : rule) (n : Node) : Prop :=
  In r (layout n).

(* A good layout has every program rule on a node somewhere AND only assigns rules from 
   the program to nodes*)
Definition good_layout (layout : Layout) (nodes : Node -> Prop) (program : list rule) : Prop :=
   Forall (fun r => exists n, nodes n /\ rule_assigned_to_node layout r n) program /\
   forall n r, nodes n /\ rule_assigned_to_node layout r n -> In r program.

(* A good forwarding function should only be able to forward things along the 
   edges *)
Definition good_forwarding (forward : ForwardingFn) (nodes : Node -> Prop) (edges : Node -> Node -> Prop) : Prop :=
  forall n1 n2 f, forward n1 f = Some n2 -> nodes n1 /\ nodes n2 /\ edges n1 n2.  

Definition good_network (net : DataflowNetwork) (program : list rule) : Prop :=
  good_graph net.(graph) /\
  good_layout net.(layout) net.(graph).(nodes) program /\
  good_forwarding net.(forward) net.(graph).(nodes) net.(graph).(edge).


(* These aren't necessarily true in general, we have to consider our layout and 
   forwarding function to make this true, but these are placeholders for now for the 
   possible coming definitions. *)

Theorem soundness (net : DataflowNetwork) (program : list rule) :
  forall f, 
  good_network net program ->
  network_prog_impl_fact net f -> Datalog.prog_impl_fact program f.
Admitted.

Theorem completeness (net : DataflowNetwork) (program : list rule) :
  forall f, Datalog.prog_impl_fact program f -> 
  good_network net program ->
  network_prog_impl_fact net f.
Admitted.

End DistributedDatalog.