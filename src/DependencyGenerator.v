(* This takes a datalog program, and for every rule, it generates the rules that it might depend on
   which will then be fed into gurobi to find an optimal layout. *)

From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Definition rel := string.
Definition var := string.
Definition fn := string.
Definition aggregator := unit.
Definition T := string.  (* semantic domain for interpretation *)
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.
Definition expr := Datalog.expr var fn.
Definition fact := Datalog.fact rel var fn.

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

(* Subst *)

Definition subst_env := list (var * expr).

Definition lookup_subst (env : subst_env) (v : var) : option expr :=
  match List.find (fun p => String.eqb (fst p) v) env with
  | Some (_, e) => Some e
  | None => None
  end.

Fixpoint do_expr_subst (env : subst_env) (e : expr) : expr :=
  match e with
  | Datalog.var_expr v =>
      match lookup_subst env v with
      | Some e' => e'
      | None => e
      end
  | Datalog.fun_expr f args =>
      Datalog.fun_expr f (map (do_expr_subst env) args)
  end.


(* Eqb *)
Fixpoint list_eqb {A : Type} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && list_eqb eqb xs ys
  | _, _ => false
  end.

Fixpoint expr_eqb (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Datalog.var_expr _, Datalog.var_expr _ =>
      true
      (* XXX: need to handle alpha equivalence here *)
  | Datalog.var_expr _, Datalog.fun_expr _ [] =>
      true
  | Datalog.fun_expr _ [], Datalog.var_expr _ =>
      true
  | Datalog.fun_expr f1 args1, Datalog.fun_expr f2 args2 =>
      String.eqb f1 f2 &&
      (fix expr_list_eqb (l1 l2 : list expr) : bool :=
         match l1, l2 with
         | [], [] => true
         | x1 :: t1, x2 :: t2 =>
             expr_eqb x1 x2 && expr_list_eqb t1 t2
         | _, _ => false
         end) args1 args2
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

Definition facts_compatible (f1 f2 : fact) : bool :=
  String.eqb (Datalog.fact_R f1) (Datalog.fact_R f2) &&
  list_eqb expr_eqb (Datalog.fact_args f1) (Datalog.fact_args f2).

Definition conc_matches_hyp (conc hyp : fact) : bool :=
  facts_compatible conc hyp.

Definition rule_concls_match_hyps (r1 r2 : rule) : bool :=
  existsb (fun conc => 
    existsb (fun hyp => conc_matches_hyp conc hyp) (Datalog.rule_hyps r2)
  ) (Datalog.rule_concls r1).

Definition rule_depends_on (r1 r2 : rule) : bool :=
  rule_concls_match_hyps r1 r2.

Definition get_rule_dependencies (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r' r) p.

Definition get_rules_dependent_on (p : program) (r : rule) : program :=
  filter (fun r' => rule_depends_on r r') p.

(* Examples! *)

Definition x_var : expr := Datalog.var_expr "x".
Definition y_var : expr := Datalog.var_expr "y".

Definition const_42 : expr := Datalog.fun_expr "42" [].
Definition const_hello : expr := Datalog.fun_expr "hello" [].

Definition add_expr : expr := Datalog.fun_expr "add" [x_var; const_42].

(* Test is_var *)
Check is_var x_var : bool.
Goal is_var x_var = true. Proof. reflexivity. Qed.

Check is_var const_42 : bool.
Goal is_var const_42 = false. Proof. reflexivity. Qed.

Check is_var add_expr : bool.
Goal is_var add_expr = false. Proof. reflexivity. Qed.

(* Test is_const *)
Check is_const x_var : bool.
Goal is_const x_var = false. Proof. reflexivity. Qed.

Check is_const const_42 : bool.
Goal is_const const_42 = true. Proof. reflexivity. Qed.

Check is_const add_expr : bool.
Goal is_const add_expr = false. Proof. reflexivity. Qed.

(* Test get_var *)
Check get_var x_var : option var.
Goal get_var x_var = Some "x". Proof. reflexivity. Qed.

Check get_var const_42 : option var.
Goal get_var const_42 = None. Proof. reflexivity. Qed.

(* Test get_const *)
Check get_const const_42 : option fn.
Goal get_const const_42 = Some "42". Proof. reflexivity. Qed.

Check get_const x_var : option fn.
Goal get_const x_var = None. Proof. reflexivity. Qed.

(* Test collect_vars *)
Check collect_vars add_expr : list var.
Goal collect_vars add_expr = ["x"]. Proof. reflexivity. Qed.

(* Test collect_consts *)
Check collect_consts add_expr : list fn.
Goal collect_consts add_expr = ["42"]. Proof. reflexivity. Qed.

(* Example fact with mixed variables and constants *)
Definition example_fact : fact :=
  {| Datalog.fact_R := "edge";
     Datalog.fact_args := [x_var; const_42; y_var] |}.

Check collect_vars_from_fact example_fact : list var.
Goal collect_vars_from_fact example_fact = ["x"; "y"]. Proof. reflexivity. Qed.

Check collect_consts_from_fact example_fact : list fn.
Goal collect_consts_from_fact example_fact = ["42"]. Proof. reflexivity. Qed.

(* ========== Examples: Alpha Equivalence ========== *)

(* Create test rules for alpha equivalence *)
Definition rule1 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "A"; fact_args := [x_var; y_var] |}
     ];
     rule_concls := [
       {| fact_R := "B"; fact_args := [x_var; y_var] |}
     ] |}.

Definition rule2 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "A"; fact_args := [const_42; y_var] |}
     ];
     rule_concls := [
       {| fact_R := "B"; fact_args := [const_42; y_var] |}
     ] |}.

Definition rule3 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "A"; fact_args := [x_var; y_var] |}
     ];
     rule_concls := [
       {| fact_R := "B"; fact_args := [x_var; y_var] |}
     ] |}.

Definition rule4 : rule :=
  {| rule_agg := None;
     rule_hyps := [
       {| fact_R := "A"; fact_args := [x_var] |}
     ];
     rule_concls := [
       {| fact_R := "B"; fact_args := [x_var; y_var] |}
     ] |}.

(* Test matching constants *)
Check facts_compatible 
  {| fact_R := "A"; fact_args := [x_var; y_var] |}
  {| fact_R := "edge"; fact_args := [const_42; y_var] |} : bool.
Goal facts_compatible 
  {| fact_R := "edge"; fact_args := [x_var; y_var] |}
  {| fact_R := "edge"; fact_args := [const_42; y_var] |} = true. 
Proof. reflexivity. Qed.

Check facts_compatible 
  {| fact_R := "edge"; fact_args := [const_42; y_var] |}
  {| fact_R := "edge"; fact_args := [const_hello; y_var] |} : bool.
Goal facts_compatible 
  {| fact_R := "edge"; fact_args := [const_42; y_var] |}
  {| fact_R := "edge"; fact_args := [const_hello; y_var] |} = false. 
Proof. reflexivity. Qed.

(* Test rule-level dependency *)
Check rule_depends_on rule1 rule2 : bool.
Goal rule_depends_on rule1 rule2 = false. Proof. reflexivity. Qed.

Check rule_depends_on rule2 rule1 : bool.
Goal rule_depends_on rule2 rule1 = false. Proof. reflexivity. Qed.

Check rule_depends_on rule1 rule4 : bool.
Goal rule_depends_on rule1 rule4 = false. Proof. reflexivity. Qed.

(* Test dependency finding *)
Definition test_program : program := [rule1; rule2; rule3; rule4].

Check get_rule_dependencies test_program rule2 : program.
Goal get_rule_dependencies test_program rule2 = []. Proof. reflexivity. Qed.

Check get_rules_dependent_on test_program rule1 : program.
Goal get_rules_dependent_on test_program rule1 = []. Proof. reflexivity. Qed.

Definition fact_edge_xy : fact :=
  {| fact_R := "A"; fact_args := [x_var; y_var] |}.

Definition fact_edge_42y : fact :=
  {| fact_R := "A"; fact_args := [const_42; y_var] |}.

Check facts_compatible fact_edge_xy fact_edge_42y : bool.
Goal facts_compatible fact_edge_xy fact_edge_42y = true. Proof. reflexivity. Qed.

Definition fact1 : fact :=
  {| Datalog.fact_R := "A";
     Datalog.fact_args := [x_var; y_var] |}.

Definition fact2 : fact :=
  {| Datalog.fact_R := "A";
     Datalog.fact_args := [const_42; y_var] |}.

Definition fact3 : fact :=
  {| Datalog.fact_R := "A";
     Datalog.fact_args := [const_42; const_hello] |}.

Definition fact4 : fact :=
  {| Datalog.fact_R := "B";
     Datalog.fact_args := [x_var; y_var] |}.

Check facts_compatible fact1 fact2 : bool.
Goal facts_compatible fact1 fact2 = true. Proof. reflexivity. Qed.

Check facts_compatible fact1 fact3 : bool.
Goal facts_compatible fact1 fact3 = true. Proof. reflexivity. Qed.

Check facts_compatible fact2 fact3 : bool.
Goal facts_compatible fact2 fact3 = true. Proof. reflexivity. Qed.

Check facts_compatible fact1 fact4 : bool.
Goal facts_compatible fact1 fact4 = false. Proof. reflexivity. Qed.

Check expr_eqb x_var (Datalog.var_expr "x") : bool.
Goal expr_eqb x_var (Datalog.var_expr "x") = true. Proof. reflexivity. Qed.

Check expr_eqb x_var y_var : bool.
Goal expr_eqb x_var y_var = true. Proof. reflexivity. Qed.

Check expr_eqb const_42 (Datalog.fun_expr "42" []) : bool.
Goal expr_eqb const_42 (Datalog.fun_expr "42" []) = true. Proof. reflexivity. Qed.

Check expr_eqb const_42 const_hello : bool.

Goal expr_eqb const_42 const_hello = false. Proof. reflexivity. Qed.
