(* This takes a datalog program, and for every rule, it generates the rules that it might depend on
   which will then be fed into gurobi to find an optimal layout. *)

From Stdlib Require Import List String Bool ZArith Lia.
From coqutil Require Import Datatypes.List Datatypes.Option Map.Interface Tactics Tactics.fwd Eqb.
From Datalog Require Import Datalog.
From Datalog.Util Require Import List Eqb.

Import ListNotations.
Open Scope bool_scope.

Section DependencyGenerator.

Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT}.
Context {var_eqb : Eqb var} {rel_eqb : Eqb rel} {fn_eqb : Eqb fn} {aggregator_eqb : Eqb aggregator}.

Context {expr_compatible : expr -> expr -> bool}.

(* Basic Utilities *)

Definition is_var (e : expr) : bool :=
  match e with
  | expr.var _ => true
  | _ => false
  end.

Definition is_const (e : expr) : bool :=
  match e with
  | expr.app _ [] => true
  | _ => false
  end.

Definition is_fun_app (e : expr) : bool :=
  match e with
  | expr.app _ (_::_) => true
  | _ => false
  end.

Definition get_var (e : expr) : option var :=
  match e with
  | expr.var v => Some v
  | _ => None
  end.

Definition get_const (e : expr) : option fn :=
  match e with
  | expr.app f [] => Some f
  | _ => None
  end.

(* Pruning.  The compiler only ever produces [rule.impl]s (the bare fragment),
   so concls/hyps are read by matching that constructor directly. *)
Definition prune_empty_concl_rules (p : list rule) : list rule :=
  filter (fun r => match r with
                   | rule.impl concls _ => negb (eqb concls [])
                   | _ => false
                   end) p.

(* Collect *)
Fixpoint collect_consts (e : expr) : list fn :=
  match e with
  | expr.var _ => []
  | expr.app f [] => [f]
  | expr.app _ args =>
      flat_map collect_consts args
  end.

Fixpoint collect_funs (e : expr) : list fn :=
  match e with
  | expr.var _ => []
  | expr.app f args =>
      f :: flat_map collect_funs args
  end.

(* Collect from a clause *)

Definition collect_consts_from_clause (c : clause) : list fn :=
  flat_map collect_consts c.(clause.args).

Definition collect_funs_from_clause (c : clause) : list fn :=
  flat_map collect_funs c.(clause.args).

Definition is_abstract (c : clause) : bool :=
  forallb is_var c.(clause.args).

Definition is_grounded_clause (c : clause) : bool :=
  forallb is_const c.(clause.args).

(* Collect for Rules.  Only [rule.impl]s arise in the bare fragment, so we
   match that constructor directly (meta/agg rules contribute nothing here). *)

Definition collect_vars_from_hyps (r : rule) : list var :=
  match r with rule.impl _ hyps => flat_map clause.vars hyps | _ => [] end.

Definition collect_vars_from_concls (r : rule) : list var :=
  match r with rule.impl concls _ => flat_map clause.vars concls | _ => [] end.

Definition collect_vars_from_rule (r : rule) : list var :=
  collect_vars_from_hyps r ++ collect_vars_from_concls r.

Definition collect_consts_from_hyps (r : rule) : list fn :=
  match r with rule.impl _ hyps => flat_map collect_consts_from_clause hyps | _ => [] end.

Definition collect_consts_from_concls (r : rule) : list fn :=
  match r with rule.impl concls _ => flat_map collect_consts_from_clause concls | _ => [] end.

Definition collect_consts_from_rule (r : rule) : list fn :=
  collect_consts_from_hyps r ++ collect_consts_from_concls r.

Definition collect_funs_from_hyps (r : rule) : list fn :=
  match r with rule.impl _ hyps => flat_map collect_funs_from_clause hyps | _ => [] end.

Definition collect_funs_from_concls (r : rule) : list fn :=
  match r with rule.impl concls _ => flat_map collect_funs_from_clause concls | _ => [] end.

Definition collect_funs_from_rule (r : rule) : list fn :=
  collect_funs_from_hyps r ++ collect_funs_from_concls r.

(* Pattern Matching.  No aggregation: a rule's hypotheses are just its
   [rule.impl] hyps (no agg hyps to append). *)

Definition get_all_hyps (r : rule) : list clause :=
  match r with rule.impl _ hyps => hyps | _ => [] end.

Definition clauses_compatible (c1 c2 : clause) : bool :=
  eqb c1.(clause.rel) c2.(clause.rel) &&
  list_eqb (aeqb := expr_compatible) c1.(clause.args) c2.(clause.args).

Definition conc_matches_hyp (conc hyp : clause) : bool :=
  clauses_compatible conc hyp.

Definition rule_concls_match_hyps (r1 r2 : rule) : bool :=
  existsb (fun conc =>
    existsb (fun hyp => conc_matches_hyp conc hyp) (get_all_hyps r2)
  ) (match r1 with rule.impl concls _ => concls | _ => [] end).

Definition rule_depends_on (r1 r2 : rule) : bool :=
  rule_concls_match_hyps r1 r2.

Definition get_rule_dependencies (p : list rule) (r : rule) : list rule :=
  filter (fun r' => rule_depends_on r' r) p.

Definition get_rules_dependent_on (p : list rule) (r : rule) : list rule :=
  filter (fun r' => rule_depends_on r r') p.

Definition rel_appears_in_hyps (R : rel) (r : rule) : bool :=
  existsb (fun c => eqb c.(clause.rel) R)
    (match r with rule.impl _ hyps => hyps | _ => [] end).

Definition rel_appears_in_concls (R : rel) (r : rule) : bool :=
  existsb (fun c => eqb c.(clause.rel) R)
    (match r with rule.impl concls _ => concls | _ => [] end).

(* Program Dependencies *)

Definition get_program_dependencies (p : list rule) : list (rule * list rule) :=
  map (fun r => (r, get_rule_dependencies p r)) p.

Definition get_program_dependencies_by_index (p : list rule) : list (nat * list nat) :=
  let fix aux lst n :=
      match lst with
      | [] => []
      | r :: rs =>
          let deps := get_rule_dependencies p r in
          let dep_indices :=
            flat_map (fun dep =>
                        match index_of dep p with
                        | Some idx => [idx]
                        | None => []
                        end) deps
          in
          (n, dep_indices) :: aux rs (n + 1)
      end
  in aux p 0.

Definition get_program_dependencies_flat (p : list rule) : list (nat * nat) :=
  flat_map (fun '(n, deps) => List.map (fun idx => (n, idx)) deps)
           (get_program_dependencies_by_index p).

Definition get_program_input_rels (p : list rule) : list rel :=
  dedup (flat_map rule.hyp_rels p).

Definition get_program_output_rels (p : list rule) : list rel :=
  dedup (flat_map rule.concl_rels p).

Definition get_input_rels_depedencies (p : list rule) : list (rel * list rule) :=
  map (fun R =>
         let dependent_rules := filter (fun r => rel_appears_in_hyps R r) p in
         (R, dependent_rules))
      (get_program_input_rels p).

Definition get_input_rels_depedencies_by_index (p : list rule) : list (nat * list nat) :=
  let input_rels := get_program_input_rels p in
  let fix aux rels n :=
      match rels with
      | [] => []
      | R :: Rs =>
          let dependent_rules := filter (fun r => rel_appears_in_hyps R r) p in
          let dependent_rule_indices :=
            flat_map (fun r =>
                        match index_of r p with
                        | Some idx => [idx]
                        | None => []
                        end) dependent_rules
          in
          (n, dependent_rule_indices) :: aux Rs (n + 1)
      end
  in aux input_rels 0.

Definition get_input_rels_depedencies_flat (p : list rule) : list (nat * nat) :=
  flat_map (fun '(rel_idx, rule_indices) =>
               List.map (fun rule_idx => (rel_idx, rule_idx)) rule_indices)
           (get_input_rels_depedencies_by_index p).

Definition get_output_rels_dependencies (p : list rule) : list (rel * list rule) :=
  map (fun R =>
         let producing_rules := filter (fun r => rel_appears_in_concls R r) p in
         (R, producing_rules))
      (get_program_output_rels p).

Definition get_output_rels_dependencies_by_index (p : list rule) : list (nat * list nat) :=
  let output_rels := get_program_output_rels p in
  let output := get_program_output_rels p in
  let fix aux rels n :=
      match rels with
      | [] => []
      | R :: Rs =>
          let producing_rules := filter (fun r => rel_appears_in_concls R r) p in
          let producing_rule_indices :=
            flat_map (fun r =>
                        match index_of r p with
                        | Some idx => [idx]
                        | None => []
                        end) producing_rules
          in
          (n, producing_rule_indices) :: aux Rs (n + 1)
      end
  in aux output_rels 0.

Definition get_output_rels_dependencies_flat (p : list rule) : list (nat * nat) :=
  flat_map (fun '(rel_idx, rule_indices) =>
               List.map (fun rule_idx => (rule_idx, rel_idx)) rule_indices)
           (get_output_rels_dependencies_by_index p).

End DependencyGenerator.
