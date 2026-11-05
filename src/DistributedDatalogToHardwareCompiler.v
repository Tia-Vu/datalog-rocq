From Stdlib Require Import String List Bool ZArith.
From coqutil Require Import Datatypes.List Datatypes.ListSet Map.Interface Map.Properties Result Eqb Tactics.fwd.
From Datalog Require Import Datalog Eqb.
From Datalog.Util Require Import List Map Default.
From DatalogRocq Require Import Topologies.Graph DependencyGenerator MapInstances ComputableGraph Acyclic VariableOrdering.
From GraphSearch Require Import GraphInterface Examples Trees.
From DatalogRocq Require Export HardwareProgram DistributedHardwareProgram.

Open Scope result_monad_scope.
Open Scope error_scope.
Open Scope bool_scope.
Import ListNotations.

Module vnode.
  Variant vnode {node_id : node_idT} :=
    | fact_dst (_ : node_id)
    | at_port (_ : node_id) (src : fwd_from)
    | ext_input
    | ext_output.

  Definition target_of {node_id : node_idT} (n : node_id) (dst : fwd_to) :=
    match dst with
    | fwd_to.output => vnode.ext_output
    | fwd_to.self => vnode.fact_dst n
    | fwd_to.node n' ch => vnode.at_port n' (fwd_from.node n ch)
    end.

  Scheme Boolean Equality for vnode.
  Section eqb.
    Context {node_id : node_idT} {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.
    #[export] Instance eqb : Eqb vnode := vnode_beq _ eqb.
    #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.
  End eqb.
End vnode. Export (hints) vnode. Abbreviation vnode := vnode.vnode.

#[local] Existing Instance rel_id.
#[local] Existing Instance no_fns.
#[local] Existing Instance no_agg.

Module Import RM := ResultMonadNotations.
Section DistributedDatalogToHardwareCompiler.
Context `{exprvar : exprvarT} {var_eqb : Eqb exprvar} {var_eqb_ok : Eqb_ok var_eqb}.
Context {node_id : node_idT} {node_id_eqb : Eqb node_id}.

Context {map_node_id_unit : map.map node_id unit} {map_node_id_unit_ok : map.ok map_node_id_unit}.
Context {map_node_id_list_rule : map.map node_id (list rule)}.
Context {map_rel_id_list_node_id : map.map rel_id (list node_id)}.
Context {map_rel_id_fwd_from_list_fwd_to : map.map (rel_id * fwd_from) (list fwd_to)}.
Context {graph_vnode : graph.graph vnode}.
Context {graph_node_id : graph.graph node_id}.
Context {map_node_id_node_info : map.map node_id node_info}.

(* the reference program a layout induces: every rule placed on any node, unioned. *)
Definition source_program (layout : partial_map node_id (list rule)) : list rule :=
  concat (values layout).

Definition layout_distributes_program (p : list rule) layout :=
  incl (source_program layout) p /\ incl p (source_program layout).

Definition layout_distributes_programb p layout :=
  inclb (source_program layout) p && inclb p (source_program layout).
Lemma layout_distributes_programb_spec p layout :
  layout_distributes_programb p layout = true -> layout_distributes_program p layout.
Proof. intros. fwd. cbv [layout_distributes_program]. auto. Qed.

(*----Forwarding Tables----*)

Context {node_ftable_map : map.map node_id forwarding_table}.

Context {rels_at_node : map.map node_id (list rel_id)}.

Definition get_internal_producers_of (layout : partial_map node_id (list rule)) :=
  let internally_produced_at_node :=
    (*maps node n to set of rels which may be (internally) produced at n*)
    map.map_values (fun p => dedup (flat_map rule.concl_rels p)) layout in
  (*maps rel R to set of nodes which may (internally) produce R*)
  invert internally_produced_at_node.

Definition get_all_producers_of layout (input_relations : list rel_id) : partial_map rel_id (list vnode) :=
  let internal_producers := get_internal_producers_of layout in
  union_with
    (list_union eqb)
    (map.map_values (fun nodes => List.map (fun n => vnode.at_port n fwd_from.self) nodes) internal_producers)
    (map.of_list (List.map (fun R => (R, [vnode.ext_input])) input_relations)).

Definition get_internal_consumers_of (layout : partial_map node_id (list rule)) :=
  let internally_consumed_at_node :=
    (*maps node n to set of rels which may be (internally) consumed at n*)
    map.map_values (fun p => dedup (flat_map rule.hyp_rels p)) layout in
  (*maps rel R to set of nodes which may (internally) consume R*)
  invert internally_consumed_at_node.

Definition get_all_consumers_of layout (output_relations : list rel_id) : partial_map rel_id (list vnode) :=
  let internal_consumers := get_internal_consumers_of layout in
  union_with
    (list_union eqb)
    (map.map_values (fun nodes => List.map vnode.fact_dst nodes) internal_consumers)
    (map.of_list (List.map (fun R => (R, [vnode.ext_output])) output_relations)).

Definition graph_of_ftable_at (n : node_id) (ft : forwarding_table) (R : rel_id) : list (vnode * vnode) :=
  flat_map
    (fun '((R', src), dsts) =>
       if eqb R R' then
         (*add src -> dst for each dst *)
         List.map (fun dst => (vnode.at_port n src, vnode.target_of n dst)) dsts
       else [])
    (map.tuples ft).

Definition graph_of_ftables_at (input_locations : list node_id) (ftables : partial_map node_id forwarding_table) (R : rel_id) : list (vnode * vnode) :=
  flat_map
    (fun '(n, ft) => graph_of_ftable_at n ft R) (map.tuples ftables) ++
    List.map (fun ext_prod => (vnode.ext_input, vnode.at_port ext_prod fwd_from.input))
    input_locations.

(*all rule_producers(R) -> all rule_consumers(R)*)
(*also should check that internal rule_consumers only receive a given message once---
 by checking that we have trees*)
(*note that the treeness is currently unnecessary for the correctness proof,
  but it will be necessary once we incorporate aggregation*)
(*TODO: also check that the edge dependency graph is acyclic
  (another thing that's currently unnecessary for the correctness proof).*)
Definition all_consumers_fed_for_relation (g : graph vnode)
  (all_producers : list vnode) (all_consumers : list vnode) :=
  forallb (fun p =>
             (*graph.check_locally_tree g p &&*)
             (*^note: this check currently fails on all the examples, since inputs are sent duplicatively.
               not completely clear what to do about this.*)
             inclb all_consumers (graph.get_reachable_nodes g p)) all_producers.

Definition all_consumers_fed (g : rel_id -> graph vnode)
  (all_producers_of : partial_map rel_id (list vnode))
  (all_consumers_of : partial_map rel_id (list vnode)) :=
  map.forallb (fun R consumers =>
                 let all_producers := get_or_default all_producers_of R in
                 all_consumers_fed_for_relation (g R) all_producers consumers)
    all_consumers_of.

Definition check_ftables_routable ftables
  (input_locations : partial_map rel_id (list node_id))
  (all_producers_of all_consumers_of : partial_map rel_id (list vnode)) : Result.result unit :=
  let vnode_graph R := graph.of_edges (graph_of_ftables_at (get_or_default input_locations R) ftables R) in
  if all_consumers_fed vnode_graph all_producers_of all_consumers_of
  then Success tt
  else error:("compile: the forwarding tables do not route some relation from one of its producers to one of its consumers").

(* The channel dependency graph: an arrival resource depends on each resource it forwards into.
   Unioned over relations, because one queue carries every relation it is keyed for. *)
Definition cdg_of_ftable_at (n : node_id) (ft : forwarding_table) : list (vnode * vnode) :=
  flat_map
    (fun '((_, src), dsts) =>
       List.map (fun dst => (vnode.at_port n src, vnode.target_of n dst)) dsts)
    (map.tuples ft).

Definition cdg_of_ftables (ftables : partial_map node_id forwarding_table) : list (vnode * vnode) :=
  flat_map (fun '(n, ft) => cdg_of_ftable_at n ft) (map.tuples ftables).

(* Dally and Seitz 1986 Theorem 1: an acyclic channel dependency graph cannot deadlock. *)
Definition check_ftables_acyclic (ftables : partial_map node_id forwarding_table)
  : Result.result unit :=
  if acyclicb (cdg_of_ftables ftables)
  then Success tt
  else error:("compile: the channel dependency graph has a cycle---these forwarding tables can deadlock").

(*----Final Compilation----*)
Definition compile_rules (rules : list rule) : list trie_rule :=
  trie_rule.of_rules (map order_variables rules).

Definition compile_node (program : list rule) (ft : forwarding_table) : node_info :=
  let ordered_rules := map order_variables program in
  {| node_info.program := trie_rule.of_rules ordered_rules;
    node_info.forwarding := ft;
    node_info.tries := trie.of_rules ordered_rules; |}.

Definition compile_all_nodes (layout : partial_map node_id (list rule)) (ftables : partial_map node_id forwarding_table) : partial_map node_id node_info :=
  map.of_list
    (map (fun n => (n, compile_node (get_or_default layout n) (get_or_default ftables n)))
       (list_union eqb (map.keys layout) (map.keys ftables))).

(* every node the layout assigns to is a real graph node. *)
Definition layout_in_graphb (g : ComputableGraph node_id) (llayout : partial_map node_id (list rule)) :=
  map.forallb (fun n _ => check_node_valid n (ComputableGraph.nodes g)) llayout.

Definition hops_in_graphb R
  (output_locations : partial_map rel_id (list node_id))
  (g : ComputableGraph node_id)
  (n : node_id) (hops : list fwd_to) :=
  forallb (fun dst => match dst with
                   | fwd_to.output => inb n (get_or_default output_locations R)
                   | fwd_to.self => true
                   | fwd_to.node dst_node _ =>
                       check_edge_exists n dst_node (ComputableGraph.edges g)
                   end) hops.

Definition ftable_in_graphb (output_locations : partial_map rel_id (list node_id)) (g : ComputableGraph node_id) (n : node_id) (ft : forwarding_table) :=
  map.forallb (fun '(R, _) hops => hops_in_graphb R output_locations g n hops) ft.

Definition ftables_in_graphb output_locations (g : ComputableGraph node_id) (ftables : node_ftable_map) : bool :=
  map.forallb (ftable_in_graphb output_locations g) ftables.

Definition compile
  (layout : partial_map node_id (list rule))
  (output_locations input_locations : partial_map rel_id (list node_id))
  (ftables : node_ftable_map)
  (g : ComputableGraph node_id) : Result.result (partial_map node_id node_info) :=
  (if check_graph_valid g
   then Success tt
   else error:("compile: the topology graph is not valid (edges reference missing nodes)")) ;;
  (if layout_in_graphb g layout
   then Success tt
   else error:("compile: a node the layout assigns rules to is not in the topology graph")) ;;
  (if ftables_in_graphb output_locations g ftables
   then Success tt
   else error:("compile: the forwarding table routes over a link the topology graph does not have, or outputs a relation at a node that is not one of its output locations")) ;;
  (*here is an assumption:*)
  let output_relations := map.keys output_locations in
  (*here is another assumption:*)
  let input_relations := map.keys input_locations in
  let all_producers_of := get_all_producers_of layout input_relations in
  let all_consumers_of := get_all_consumers_of layout output_relations in
  check_ftables_routable ftables input_locations all_producers_of all_consumers_of ;;
  check_ftables_acyclic ftables ;;
  Success (compile_all_nodes layout ftables).

Definition dumb_ftable_at_node' (output_locations : partial_map rel_id (list node_id)) R node neighbors :
  list (fwd_from * (list fwd_to)) :=
  let to_all neighbors0 := (if inb node (get_or_default output_locations R) then [fwd_to.output] else []) ++
                             fwd_to.self :: List.map (fun neighbor => fwd_to.node neighbor O) neighbors0 in
  (fwd_from.input, to_all neighbors) :: (fwd_from.self, to_all neighbors)
    :: List.map (fun '(picked, rest) => (fwd_from.node picked O, to_all rest)) (picks neighbors).

Definition dumb_ftable_at_node output_locations all_rels node neighbors : forwarding_table :=
  map.of_list (flat_map (fun R => List.map (fun '(from, to) => ((R, from), to)) (dumb_ftable_at_node' output_locations R node neighbors)) all_rels).

Fixpoint dumb_ftables_for_tree output_locations all_rels (parent : option node_id) (t : tree node_id) : list (node_id * forwarding_table) :=
  match t with
  | tree_cons rt children => (rt, dumb_ftable_at_node output_locations all_rels rt (option_to_list parent ++ List.map root children)) :: flat_map (dumb_ftables_for_tree output_locations all_rels (Some rt)) children
  end.

Definition dumb_ftables (g : ComputableGraph node_id) output_locations (all_rels : list rel_id) : node_ftable_map :=
  match map.keys g.(nodes) with
  | [] => map.empty
  | root :: _ => map.of_list (dumb_ftables_for_tree output_locations all_rels None (tree_of g.(edges) root))
  end.

Definition compile_with_dumb_ftables
  (layout : partial_map node_id (list rule))
  (output_locations input_locations : partial_map rel_id (list node_id))
  (g : ComputableGraph node_id) : Result.result (partial_map node_id node_info) :=
  let ftables := dumb_ftables g output_locations (map.keys (get_all_producers_of layout (map.keys input_locations))) in
  compile layout output_locations input_locations ftables g.
End DistributedDatalogToHardwareCompiler.
