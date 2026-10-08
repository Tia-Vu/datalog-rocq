From Stdlib Require Import String List Bool ZArith.
From coqutil Require Import Datatypes.List Datatypes.ListSet Map.Interface Map.Properties Result Eqb Tactics.fwd.
From Datalog Require Import Datalog Eqb.
From Datalog.Util Require Import List Map Default.
From DatalogRocq Require Import Topologies.Graph DependencyGenerator MapInstances ComputableGraph.
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

Module Import RM := ResultMonadNotations.
Section DistributedDatalogToHardwareCompiler.
Context `{params : datalog_params}.
Context {node_id : node_idT} {node_id_eqb : Eqb node_id}.

Context {map_node_id_unit : map.map node_id unit} {map_node_id_unit_ok : map.ok map_node_id_unit}.
Context {map_node_id_lowered_program : map.map node_id lowered_program}.
Context {map_rel_id_list_node_id : map.map rel_id (list node_id)}.
Context {map_rel_id_fwd_from_list_fwd_to : map.map (rel_id * fwd_from) (list fwd_to)}.
Context {graph_vnode : graph.graph vnode}.
Context {graph_node_id : graph.graph node_id}.

Record node_context := {
  nctries : list trie;
  last_trie_id : trie_id;
}.

(*---- var_graph as ComputableGraph over var ----*)
Context {var_node_set : map.map exprvar unit}.
Context {var_node_set_ok : map.ok var_node_set}.
Context {var_graph_impl : graph.graph exprvar} {var_graph_impl_ok : graph.ok var_graph_impl}.

(* the reference program a layout induces: every rule placed on any node, unioned. *)
Definition source_program (layout : partial_map node_id (list lowered_rule)) : list lowered_rule :=
  concat (values layout).

Definition layout_distributes_program (p : list lowered_rule) layout :=
  incl (source_program layout) p /\ incl p (source_program layout).

Definition layout_distributes_programb p layout :=
  inclb (source_program layout) p && inclb p (source_program layout).
Lemma layout_distributes_programb_spec p layout :
  layout_distributes_programb p layout = true -> layout_distributes_program p layout.
Proof. intros. fwd. cbv [layout_distributes_program]. auto. Qed.

(*----Stuff to keep default ordering (if desired) ----*)

Definition hyp_var_order (hyps : list lowered_fact) : list exprvar :=
  dedup (flat_map clause.vars hyps).

(*----Variable ordering----*)

Definition vg_neighbors (g : ComputableGraph exprvar) (v : exprvar) : list exprvar :=
  graph.edges g.(edges) v.

Fixpoint add_arg_edges (arg : lowered_expr) (g : ComputableGraph exprvar) (clause_vars : var_node_set) : ComputableGraph exprvar :=
  match arg with
  | expr.var v =>
    let g' := {| nodes := map.put g.(nodes) v tt;
                 edges := graph.put_edges g.(edges) v (map.keys clause_vars) |} in
    (* Add reverse edges: for each u in clause_vars, add edge u -> v *)
    map.fold (fun acc u _ =>
      {| nodes := acc.(nodes); edges := graph.put acc.(edges) u v |})
      g' clause_vars
  | expr.app _ args =>
    fold_left (fun acc arg => add_arg_edges arg acc clause_vars) args g
  end.

Fixpoint add_args_edges (args : list lowered_expr) (g : ComputableGraph exprvar) (seen : var_node_set) : ComputableGraph exprvar :=
  match args with
  | [] => g
  | arg :: rest =>
    let g' := add_arg_edges arg g seen in
    let seen' := match arg with
                 | expr.var v => map.put seen v tt
                 | expr.app _ _ => seen
                 end in
    add_args_edges rest g' seen'
  end.

Definition add_hyp_edges (hyp : lowered_fact) (g : ComputableGraph exprvar) : ComputableGraph exprvar :=
  add_args_edges hyp.(clause.args) g map.empty.

Definition empty_ComputableGraph : ComputableGraph exprvar :=
  {| nodes := map.empty; edges := graph.empty |}.

Definition create_dependency_graph (hyps : list lowered_fact) : ComputableGraph exprvar :=
  fold_left (fun acc hyp => add_hyp_edges hyp acc) hyps empty_ComputableGraph.

Definition compute_degree (g : ComputableGraph exprvar) (v : exprvar) : nat :=
  length (vg_neighbors g v).

Definition compute_degree_to_visited_set (g : ComputableGraph exprvar) (visited : var_node_set) (v : exprvar) : nat :=
  fold_left (fun acc neighbor =>
    match map.get visited neighbor with
    | Some _ => S acc
    | None => acc
    end) (vg_neighbors g v) 0.

Definition compute_max_degree_var_to_visited_set (g : ComputableGraph exprvar) (visited : var_node_set)
    : option (exprvar * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree_to_visited_set g visited v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

Definition compute_max_degree_var (g : ComputableGraph exprvar) : option (exprvar * nat) :=
  map.fold (fun acc v _ =>
    let degree := compute_degree g v in
    match acc with
    | None => Some (v, degree)
    | Some (_, max_degree) => if Nat.ltb max_degree degree then Some (v, degree) else acc
    end) None g.(nodes).

(* If we want to enforce a specific order for tie breaks *)
Definition compute_max_degree_var_to_visited_set_ordered
    (g : ComputableGraph exprvar) (visited : var_node_set) (candidates : list exprvar)
    : option (exprvar * nat) :=
  fold_left (fun acc v =>
    (* Only consider vars still in the dep_graph *)
    match map.get g.(nodes) v with
    | None => acc
    | Some _ =>
      let degree := compute_degree_to_visited_set g visited v in
      match acc with
      | None => Some (v, degree)
      | Some (_, max_degree) =>
        if Nat.ltb max_degree degree then Some (v, degree) else acc
      end
    end) candidates None.

Definition compute_max_degree_var_ordered
    (g : ComputableGraph exprvar) (candidates : list exprvar) : option (exprvar * nat) :=
  fold_left (fun acc v =>
    match map.get g.(nodes) v with
    | None => acc
    | Some _ =>
      let degree := compute_degree g v in
      match acc with
      | None => Some (v, degree)
      | Some (_, max_degree) =>
        if Nat.ltb max_degree degree then Some (v, degree) else acc
      end
    end) candidates None.

Definition remove_edge_from_graph (g : ComputableGraph exprvar) (v1 v2 : exprvar) : ComputableGraph exprvar :=
  {| nodes := g.(nodes);
     edges := graph.remove (graph.remove g.(edges) v1 v2) v2 v1 |}.

Definition remove_edges_touching_var (g : ComputableGraph exprvar) (v : exprvar) : ComputableGraph exprvar :=
  fold_left (fun acc neighbor => remove_edge_from_graph acc v neighbor) (vg_neighbors g v) g.

Record ordering_context := {
  dep_graph : ComputableGraph exprvar;
  order : list exprvar;
  visited : var_node_set;
}.

Definition visit_node (v : exprvar) (ctx : ordering_context) : ordering_context :=
  {| dep_graph := {| nodes := map.remove ctx.(dep_graph).(nodes) v;
                     edges := (remove_edges_touching_var ctx.(dep_graph) v).(edges) |};
     order := v :: ctx.(order);
     visited := map.put ctx.(visited) v tt |}.

Definition initial_ordering_context (g : ComputableGraph exprvar) : ordering_context :=
  {| dep_graph := g; order := []; visited := map.empty |}.

Definition choose_next_var (ctx : ordering_context) : option exprvar :=
  match compute_max_degree_var_to_visited_set ctx.(dep_graph) ctx.(visited) with
  | Some (v, _) => Some v
  | None =>
    match compute_max_degree_var ctx.(dep_graph) with
    | Some (v, _) => Some v
    | None => None
    end
  end.

Definition choose_next_var_ordered (ctx : ordering_context) (candidates : list exprvar) : option exprvar :=
  match compute_max_degree_var_to_visited_set_ordered ctx.(dep_graph) ctx.(visited) candidates with
  | Some (v, _) => Some v
  | None =>
    match compute_max_degree_var_ordered ctx.(dep_graph) candidates with
    | Some (v, _) => Some v
    | None => None
    end
  end.

Fixpoint compute_variable_ordering_h (ctx : ordering_context) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var ctx with
    | Some v => compute_variable_ordering_h (visit_node v ctx) fuel'
    | None => ctx
    end
  end.

Fixpoint compute_variable_ordering_ordered_h (ctx : ordering_context)
  (candidates : list exprvar) (fuel : nat) : ordering_context :=
  match fuel with
  | O => ctx
  | S fuel' =>
    match choose_next_var_ordered ctx candidates with
    | Some v => compute_variable_ordering_ordered_h (visit_node v ctx) candidates fuel'
    | None => ctx
    end
  end.

Definition compute_variable_ordering_ordered (g : ComputableGraph exprvar) (hyps : list lowered_fact) : list exprvar :=
  let candidates := hyp_var_order hyps in
  rev
    (compute_variable_ordering_ordered_h (initial_ordering_context g)
       candidates (length candidates)).(order).

(*----Trie Allocation----*)

Definition vars_of_arg (arg : lowered_expr) : list exprvar :=
  match arg with
  | expr.var v => [v]
  | expr.app _ _ => []
  end.

Definition compute_var_order (lf : lowered_fact) : list exprvar :=
  flat_map vars_of_arg lf.(clause.args).

Context {var_idx_map : map.map exprvar nat}.

Fixpoint build_base_map (desired_order : list exprvar) (original_order : list exprvar)
    (offset : nat) (m : var_idx_map) : var_idx_map :=
  match desired_order with
  | [] => m
  | v :: vs =>
    build_base_map vs original_order
      (offset + count_occ v original_order)
      (map.put m v offset)
  end.

Fixpoint compute_perm_aux (original_order : list exprvar) (base_map occ_map : var_idx_map) : list nat :=
  match original_order with
  | [] => []
  | v :: vs =>
    let base := get_or_default base_map v in
    let occ  := get_or_default occ_map v in
    (base + occ) :: compute_perm_aux vs base_map (map.put occ_map v (occ + 1))
  end.

Definition compute_permutation (original_order desired_order : list exprvar) : permutation :=
  compute_perm_aux original_order
    (build_base_map desired_order original_order 0 map.empty) map.empty.

(*----Trie Generation----*)

Definition update_node_context_with_trie (t : trie) (ncontext : node_context) : node_context :=
  {| nctries := t :: ncontext.(nctries);
     last_trie_id := S ncontext.(last_trie_id) |}.

Definition generate_trie (hyp : lowered_fact) (rule_var_order : list exprvar)
    (existing_tries : list trie)
    (ncontext : node_context) : trie * node_context :=
  let perm := compute_permutation (compute_var_order hyp) rule_var_order in
  let rel_id := hyp.(clause.rel) in
  match find (fun t =>
    eqb t.(trel) rel_id && eqb t.(tperm) perm) existing_tries with
  | Some t => (t, ncontext)
  | None =>
    let new_trie := {| tid := ncontext.(last_trie_id); trel := rel_id; tperm := perm |} in
    (new_trie, update_node_context_with_trie new_trie ncontext)
  end.

Definition get_rule_var_index (rule_var_order : list exprvar) (v : exprvar) : Result.result nat :=
  match index_of v rule_var_order with
  | Some idx => Success idx
  | None => error:("get_rule_var_index: variable not found in rule_var_order")
  end.

Definition generate_join (tries_by_hyp : list trie) (v : exprvar) (hyps : list lowered_fact) : join :=
  let entries :=
    flat_map (fun '(clause, t, hyp) =>
                List.map (fun arg_idx => (t.(tid), nth arg_idx t.(tperm) 0, clause))
                         (indexes_of (expr.var v) hyp.(clause.args)))
             (combine3 (seq 0 (length hyps)) tries_by_hyp hyps) in
  {| tries := List.map fst3 entries;
     trie_levels := List.map snd3 entries;
     clauses := List.map thd3 entries |}.

Definition generate_query (tries : list trie) (rule_var_order : list exprvar)
    (hyps : list lowered_fact) : query :=
  List.map (fun v => generate_join tries v hyps) rule_var_order.

Definition compile_hyps (hyps : list lowered_fact) (rule_var_order : list exprvar)
    (existing_tries : list trie) (ncontext : node_context)
    : query * node_context :=
  (* [pool] is the dedup pool threaded into [generate_trie] (existing tries followed by
     the ones we generate, newest first).  [per_hyp_rev] is the trie chosen for each
     hypothesis, in reverse hypothesis order.  These must be kept distinct: [generate_join]
     pairs its trie list with [hyps] positionally, so the list handed to [generate_query]
     must be the *per-hypothesis* tries in forward order — not the reversed pool. *)
  let '(pool, per_hyp_rev, ncontext) :=
    fold_left (fun '(pool, per_hyp_rev, ncontext) hyp =>
      let (t, ncontext) := generate_trie hyp rule_var_order pool ncontext in
      (t :: pool, t :: per_hyp_rev, ncontext)) hyps (existing_tries, [], ncontext) in
  (generate_query (rev per_hyp_rev) rule_var_order hyps, ncontext).

Definition initial_node_context : node_context :=
  {| nctries := []; last_trie_id := 0 |}.

Definition compile_concl (concl : lowered_fact)
    (rule_var_order : list exprvar) : Result.result join_output :=
  var_indices <- List.all_success (List.map (fun arg =>
    match arg with
    | expr.var v => get_rule_var_index rule_var_order v
    | expr.app _ _ => Success 0
    end) concl.(clause.args)) ;;
  Success {| output_rel := concl.(clause.rel);
             output_var_indices := var_indices |}.

Definition compile_concls (concls : list lowered_fact)
    (rule_var_order : list exprvar) : Result.result (list join_output) :=
  List.all_success (List.map (fun concl => compile_concl concl rule_var_order) concls).

(* Version that tries to keep original ordering.  Bare fragment: only
   [rule.impl]s are compiled. *)
Definition compile_rule (rule : lowered_rule)
    (ncontext : node_context) : Result.result (hardware_rule * node_context) :=
  match rule with
  | rule.impl rconcls rhyps =>
    let dep_g := create_dependency_graph rhyps in
    let rule_var_order := compute_variable_ordering_ordered dep_g rhyps in  (* pass hyps for ordering *)
    let '(query, ncontext) :=
      compile_hyps rhyps rule_var_order ncontext.(nctries) ncontext in
    concls <- compile_concls rconcls rule_var_order ;;
    Success ({| hhyps := query; hconcls := concls;
                hsig := List.map (fun h => (h.(clause.rel), length h.(clause.args))) rhyps |}, ncontext)
  | _ => error:("compile_rule: aggregation/meta rules are not supported")
  end.

(*----Forwarding Tables----*)

Context {node_ftable_map : map.map node_id forwarding_table}.

Context {rels_at_node : map.map node_id (list rel_id)}.

Definition get_internal_producers_of (layout : partial_map node_id (list lowered_rule)) :=
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

Definition get_internal_consumers_of (layout : partial_map node_id (list lowered_rule)) :=
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

(*----Final Compilation----*)

Definition compile_node (node : node_id) (program : lowered_program) : Result.result node_info :=
  '(compiled_rules, ncontext) <-
    fold_left (fun acc rule =>
      '(rules, ncontext) <- acc ;;
      '(hr, ncontext) <- compile_rule rule ncontext ;;
      Success (hr :: rules, ncontext)%list
    ) program (Success ([], initial_node_context)) ;;
  Success {| nid := node;
             nprogram := rev compiled_rules;
             nforwarding := map.empty;
             ntries := rev ncontext.(nctries) |}.

Definition compile_all_nodes (llayout : partial_map node_id (list lowered_rule)) : Result.result (list node_info) :=
  List.all_success (List.map (fun '(node, program) => compile_node node program) (map.tuples llayout)).

(* Attach the compiled forwarding tables to node_infos -- now for EVERY node that forwards, not
   just the layout nodes: layout nodes keep their compiled program/tries, and any extra node that
   appears as a forwarding source (a key of [ftables], e.g. a fact-only input node) gets an empty
   program/tries with its forwarding table.  This makes the returned [ninfos] self-contained: the
   whole distributed network (programs, tries AND forwarding) can be read back off it. *)
Definition attach_forwarding_tables (ninfos : list node_info)
    (ftables : node_ftable_map) : list node_info :=
  List.map (fun ninfo =>
    {| nid := ninfo.(nid);
       nprogram := ninfo.(nprogram);
       nforwarding := get_or_default ftables ninfo.(nid);
       ntries := ninfo.(ntries) |}
  ) ninfos
  ++ List.map (fun n =>
       {| nid := n;
          nprogram := [];
          nforwarding := get_or_default ftables n ;
          ntries := [] |})
     (filter
        (fun n => negb (existsb (fun ninfo => eqb ninfo.(nid) n) ninfos))
        (map.keys ftables)).

(* every node the layout assigns to is a real graph node. *)
Definition layout_in_graphb (g : ComputableGraph node_id) (llayout : partial_map node_id (list lowered_rule)) :=
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
  (layout : partial_map node_id (list lowered_rule))
  (output_locations input_locations : partial_map rel_id (list node_id))
  (ftables : node_ftable_map)
  (g : ComputableGraph node_id) : Result.result (list node_info) :=
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
  ninfos <- compile_all_nodes layout ;;
  Success (attach_forwarding_tables ninfos ftables).

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
  (layout : partial_map node_id (list lowered_rule))
  (output_locations input_locations : partial_map rel_id (list node_id))
  (g : ComputableGraph node_id) : Result.result (list node_info) :=
  let ftables := dumb_ftables g output_locations (map.keys (get_all_producers_of layout (map.keys input_locations))) in
  compile layout output_locations input_locations ftables g.
End DistributedDatalogToHardwareCompiler.

Compute compute_permutation [2;3;1;1] [1;2;3].
Compute generate_join
  [ {| tid := 0; trel := 0; tperm := [0; 1] |} ;
    {| tid := 1; trel := 0; tperm := [1; 0] |} ]
  1
  [ {| clause.rel := 0; clause.args := [expr.var 0; expr.var 1] |} ;
    {| clause.rel := 0; clause.args := [expr.var 1; expr.var 2] |} ].
