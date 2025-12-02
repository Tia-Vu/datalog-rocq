From Datalog Require Import Datalog.
From DatalogRocq Require Import DependencyGenerator.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Bool.Bool.
From Datalog Require Import ATLToDatalog.
From Stdlib Require Import ZArith.Znat.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

Module ATLDatalogParams.

Definition rel := (ATLToDatalog.rel * bool)%type.
Definition var := (string + nat)%type.
Definition fn := ATLToDatalog.fn.
Definition aggregator := ATLToDatalog.aggregator.
Definition T := string.  (* semantic domain for interpretation *)
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.
Definition expr := Datalog.expr var fn.
Definition fact := Datalog.fact rel var fn.

(* Equality *)
Definition var_eqb : var -> var -> bool := ATLToDatalog.var_eqb.
Definition var_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (var_eqb x y).
Proof. apply ATLToDatalog.var_eqb_spec. Qed.

Definition ATLToDatalogRel_eqb (r1 r2 : ATLToDatalog.rel) : bool :=
  match r1, r2 with
  | str_rel s1, str_rel s2 => s1 =? s2
  | nat_rel n1, nat_rel n2 => (n1 =? n2)%nat
  | true_rel, true_rel => true
  | _, _ => false
  end.

Definition ATLToDatalogRel_eqb_spec x y : BoolSpec (x = y) (x <> y) (ATLToDatalogRel_eqb x y).
Proof.
    destruct x, y; simpl; try (constructor; congruence).
    - destruct (String.eqb_spec s s0); constructor; congruence.
    - destruct (Nat.eqb_spec n n0); constructor; congruence.
Qed.

Definition rel_eqb (r1 r2 : rel) : bool :=
    match r1, r2 with
    | (rel1, b1), (rel2, b2) =>
        ATLToDatalogRel_eqb rel1 rel2 && Bool.eqb b1 b2
    end.

Lemma pair_eqb_spec {A B} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool)
      (specA : forall x y, BoolSpec (x = y) (x <> y) (eqbA x y))
      (specB : forall x y, BoolSpec (x = y) (x <> y) (eqbB x y))
      (p1 p2 : A * B) :
  BoolSpec (p1 = p2) (p1 <> p2)
           (let (a1,b1) := p1 in let (a2,b2) := p2 in eqbA a1 a2 && eqbB b1 b2).
Proof.
  destruct p1 as [a1 b1], p2 as [a2 b2].
  destruct (specA a1 a2); destruct (specB b1 b2); constructor; congruence.
Qed.

Definition rel_eqb_spec x y : BoolSpec (x = y) (x <> y) (rel_eqb x y).
Proof.
  apply pair_eqb_spec.
  - apply ATLToDatalogRel_eqb_spec.
  - intros. destruct (Bool.eqb_spec x0 y0); constructor; congruence.
Qed.

(* Fixpoint expr_compatible (e1 e2 : expr) : bool := true. *)

Definition expr_compatible (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Datalog.var_expr _, Datalog.var_expr _ =>
      true
      (* XXX: need to handle alpha equivalence here? *)
  | Datalog.var_expr _, Datalog.fun_expr _ [] =>
      true
  | Datalog.fun_expr _ [], Datalog.var_expr _ =>
      true
  | Datalog.fun_expr f1 args1, Datalog.fun_expr f2 args2 => true (* For now we don't think about function equality *)
  | _, _ => false
  end.

End ATLDatalogParams.