(* This takes a datalog program, and for every rule, it generates the rules that it might depend on
   which will then be fed into gurobi to find an optimal layout. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Module Type DatalogParams.

Parameter rel var fn aggregator T : Type.
Parameter var_eqb : var -> var -> bool.
Parameter var_eqb_spec :  forall x0 y0 : var, BoolSpec (x0 = y0) (x0 <> y0) (var_eqb x0 y0).
Parameter rel_eqb : rel -> rel -> bool.
Parameter rel_eqb_spec : forall x0 y0 : rel, BoolSpec (x0 = y0) (x0 <> y0) (rel_eqb x0 y0).

Definition expr := Datalog.expr var fn.
Definition fact := Datalog.fact rel var fn.
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.

Parameter expr_compatible : expr -> expr -> bool.

End DatalogParams.

Module DependencyGenerator (Params : DatalogParams).

Import Params.

(* Basic Utilities *)

Definition is_var (e : expr) : bool :=
  match e with
  | Datalog.var_expr _ => true
  | _ => false
  end.

Definition is_const (e : expr) : bool :=
  match e with
  | Datalog.fun_expr _ [] => true
  | _ => false
  end.

Definition is_fun_app (e : expr) : bool :=
  match e with
  | Datalog.fun_expr _ (_::_) => true
  | _ => false
  end.

Definition get_var (e : expr) : option var :=
  match e with
  | Datalog.var_expr v => Some v
  | _ => None
  end.

Definition get_const (e : expr) : option fn :=
  match e with
  | Datalog.fun_expr f [] => Some f
  | _ => None
  end.

(* Eqb *)
Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
  | _, _ => false
  end.

(* Collect *)
Fixpoint collect_vars (e : expr) : list var :=
  match e with
  | Datalog.var_expr v => [v]
  | Datalog.fun_expr _ args => 
      flat_map collect_vars args
  end.

Fixpoint collect_consts (e : expr) : list fn :=
  match e with
  | Datalog.var_expr _ => []
  | Datalog.fun_expr f [] => [f]
  | Datalog.fun_expr _ args => 
      flat_map collect_consts args
  end.

Fixpoint collect_funs (e : expr) : list fn :=
  match e with
  | Datalog.var_expr _ => []
  | Datalog.fun_expr f args => 
      f :: flat_map collect_funs args
  end.

(* Collect Fact *)

Definition collect_vars_from_fact (f : fact) : list var :=
  flat_map collect_vars (Datalog.fact_args f).

Definition collect_consts_from_fact (f : fact) : list fn :=
  flat_map collect_consts (Datalog.fact_args f).

Definition collect_funs_from_fact (f : fact) : list fn :=
  flat_map collect_funs (Datalog.fact_args f).

Definition is_abstract (f : fact) : bool :=
  forallb is_var (Datalog.fact_args f).

Definition is_grounded_fact (f : fact) : bool :=
  forallb is_const (Datalog.fact_args f).

(* Collect for Rules *)

Definition collect_vars_from_hyps (r : rule) : list var :=
  flat_map collect_vars_from_fact (Datalog.rule_hyps r).

Definition collect_vars_from_concls (r : rule) : list var :=
  flat_map collect_vars_from_fact (Datalog.rule_concls r).

Definition collect_vars_from_rule (r : rule) : list var :=
  collect_vars_from_hyps r ++ collect_vars_from_concls r.

Definition collect_consts_from_hyps (r : rule) : list fn :=
  flat_map collect_consts_from_fact (Datalog.rule_hyps r).

Definition collect_consts_from_concls (r : rule) : list fn :=
  flat_map collect_consts_from_fact (Datalog.rule_concls r).

Definition collect_consts_from_rule (r : rule) : list fn :=
  collect_consts_from_hyps r ++ collect_consts_from_concls r.

Definition collect_funs_from_hyps (r : rule) : list fn :=
  flat_map collect_funs_from_fact (Datalog.rule_hyps r).

Definition collect_funs_from_concls (r : rule) : list fn :=
  flat_map collect_funs_from_fact (Datalog.rule_concls r).

Definition collect_funs_from_rule (r : rule) : list fn :=
  collect_funs_from_hyps r ++ collect_funs_from_concls r.

Definition get_rule_concls_rels (r : rule) : list rel :=
  map (fun fact => Datalog.fact_R fact) (Datalog.rule_concls r).

Definition get_rule_hyps_rels (r : rule) : list rel :=
  map (fun fact => Datalog.fact_R fact) (Datalog.rule_hyps r).

(* Pattern Matching *)

Definition get_agg_hyps (r : rule) : list fact :=
  match Datalog.rule_agg r with
  | None => []
  | Some (_, ae) => Datalog.agg_hyps ae
  end.

Definition get_all_hyps (r : rule) : list fact :=
  Datalog.rule_hyps r ++ get_agg_hyps r.

Definition facts_compatible (f1 f2 : fact) : bool :=
  rel_eqb (Datalog.fact_R f1) (Datalog.fact_R f2) &&
  list_eqb expr_compatible (Datalog.fact_args f1) (Datalog.fact_args f2).

Definition conc_matches_hyp (conc hyp : fact) : bool :=
  facts_compatible conc hyp.

Definition rule_concls_match_hyps (r1 r2 : rule) : bool :=
  existsb (fun conc => 
    existsb (fun hyp => conc_matches_hyp conc hyp) (get_all_hyps r2)
  ) (Datalog.rule_concls r1).

Definition rule_depends_on (r1 r2 : rule) : bool :=
  rule_concls_match_hyps r1 r2.

Definition get_rule_dependencies (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r' r) p.

Definition get_rules_dependent_on (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r r') p.

Definition get_program_dependencies (p : program) : list (rule * list rule) :=
  map (fun r => (r, get_rule_dependencies p r)) p.

Definition fact_eqb (f1 f2 : fact) : bool :=
  rel_eqb (fact_R f1) (fact_R f2) &&
  list_eqb expr_compatible (fact_args f1) (fact_args f2).

Definition rule_eqb (r1 r2 : rule) : bool :=
  list_eqb fact_eqb (Datalog.rule_hyps r1) (Datalog.rule_hyps r2) &&
  list_eqb fact_eqb (Datalog.rule_concls r1) (Datalog.rule_concls r2) &&
  match Datalog.rule_agg r1, Datalog.rule_agg r2 with
  | None, None => true
  | Some (a1, ae1), Some (a2, ae2) =>
      var_eqb a1 a2 &&
      list_eqb fact_eqb (Datalog.agg_hyps ae1) (Datalog.agg_hyps ae2)
  | _, _ => false
  end.

Fixpoint lookup_rule_number (r : rule) (p : program) (n : nat) : option nat :=
  match p with
  | [] => None
  | r' :: ps =>
      if rule_eqb r r' then Some n
      else lookup_rule_number r ps (n + 1)
  end.

Definition get_program_dependencies_by_index (p : program) : list (nat * list nat) :=
  let fix aux lst n :=
      match lst with
      | [] => []
      | r :: rs =>
          let deps := get_rule_dependencies p r in
          let dep_indices :=
            flat_map (fun dep =>
                        match lookup_rule_number dep p 0 with
                        | Some idx => [idx]
                        | None => []
                        end) deps
          in
          (n, dep_indices) :: aux rs (n + 1)
      end
  in aux p 0.

Definition get_program_dependencies_flat (p : program) : list (nat * nat) :=
  flat_map (fun '(n, deps) => List.map (fun idx => (n, idx)) deps)
           (get_program_dependencies_by_index p).


End DependencyGenerator.