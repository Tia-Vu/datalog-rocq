From Datalog Require Import Datalog.
From DatalogRocq Require Import DependencyGenerator.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Bool.Bool.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Module StringDatalogParams.

Definition rel := string.
Definition var := string.
Definition fn := string.
Definition aggregator := unit.
Definition T := string.  (* semantic domain for interpretation *)
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.
Definition expr := Datalog.expr var fn.
Definition fact := Datalog.fact rel var fn.

(* Equality *)
Definition var_eqb : var -> var -> bool := String.eqb.
Definition fn_eqb : fn -> fn -> bool := String.eqb.
Definition rel_eqb : rel -> rel -> bool := String.eqb.

Lemma var_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof. apply String.eqb_spec. Qed.

Lemma fn_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (fn_eqb x y).
Proof. apply String.eqb_spec. Qed.

Lemma rel_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (rel_eqb x y).
Proof. apply String.eqb_spec. Qed.

Fixpoint expr_compatible (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Datalog.var_expr _, Datalog.var_expr _ =>
      true
      (* XXX: need to handle alpha equivalence here *)
  | Datalog.var_expr _, Datalog.fun_expr _ [] =>
      true
  | Datalog.fun_expr _ [], Datalog.var_expr _ =>
      true
  | Datalog.fun_expr f1 args1, Datalog.fun_expr f2 args2 =>
      fn_eqb f1 f2 &&
      (fix expr_list_eqb (l1 l2 : list expr) : bool :=
         match l1, l2 with
         | [], [] => true
         | x1 :: t1, x2 :: t2 =>
             expr_compatible x1 x2 && expr_list_eqb t1 t2
         | _, _ => false
         end) args1 args2
  | _, _ => false
  end.

End StringDatalogParams.