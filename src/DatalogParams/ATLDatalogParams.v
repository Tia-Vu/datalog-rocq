From Datalog Require Import Datalog.
From DatalogRocq Require Import DependencyGenerator EqbSpec.
From Stdlib Require Import List String Bool ZArith.
From Datalog Require Import ATLToDatalog.
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
Definition agg_expr := Datalog.agg_expr rel var fn aggregator.

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

Definition rel_eqb_spec x y : BoolSpec (x = y) (x <> y) (rel_eqb x y).
Proof.
  apply pair_eqb_spec.
  - apply ATLToDatalogRel_eqb_spec.
  - intros. destruct (Bool.eqb_spec x0 y0); constructor; congruence.
Qed.

Definition aggregator_eqb (a1 a2 : aggregator) : bool := true.

Definition aggregator_eqb_spec x y : BoolSpec (x = y) (x <> y) (aggregator_eqb x y).
Proof.
  destruct x, y; constructor; congruence.
Qed.

(* Right now this isn't possible because of a hiccup in Real Numbers *)

Definition Bfn_eqb (f1 f2 : Bfn) : bool :=
  match f1, f2 with
  | fn_BAnd, fn_BAnd => true
  | fn_BLt, fn_BLt => true
  | fn_BLe, fn_BLe => true
  | fn_BEq, fn_BEq => true
  | fn_BNot, fn_BNot => true
  | fn_BLit b1, fn_BLit b2 => Bool.eqb b1 b2
  | _, _ => false
  end.

Lemma Bfn_eqb_spec x y : BoolSpec (x = y) (x <> y) (Bfn_eqb x y).
Proof. 
  destruct x, y; try (constructor; congruence); simpl;
  try (destruct (Bool.eqb_spec b b0); constructor; congruence).
Qed.

Definition Zfn_eqb (f1 f2 : Zfn) : bool :=
  match f1, f2 with
  | fn_ZPlus, fn_ZPlus => true
  | fn_ZMinus, fn_ZMinus => true
  | fn_ZTimes, fn_ZTimes => true
  | fn_ZDivf, fn_ZDivf => true
  | fn_ZDivc, fn_ZDivc => true
  | fn_ZMod, fn_ZMod => true
  | fn_Zmax, fn_Zmax => true
  | fn_ZRange, fn_ZRange => true
  | fn_ZLit x, fn_ZLit y => Z.eqb x y
  | _, _ => false
  end.

Lemma Zfn_eqb_spec x y : BoolSpec (x = y) (x <> y) (Zfn_eqb x y).
Proof.
  destruct x, y; try (constructor; congruence); simpl.
  destruct (Z.eqb_spec x x0); constructor; congruence.
Qed.

Definition Rfn_eqb (f1 f2 : Rfn) : bool :=
  match f1, f2 with
  | fn_SMul, fn_SMul => true
  | fn_SAdd, fn_SAdd => true
  | fn_SDiv, fn_SDiv => true
  | fn_SSub, fn_SSub => true
  | fn_SLit x, fn_SLit y => true (* XXX : this is broken because it wants equality of R which is not decideable *)
  | _, _ => false
  end.

Lemma Rfn_eqb_spec :
  forall f1 f2,
    BoolSpec (f1 = f2) (f1 <> f2) (Rfn_eqb f1 f2).
Proof.
Admitted.

Definition fn_eqb (f1 f2 : fn) : bool :=
  match f1, f2 with
  | fn_B b1, fn_B b2 => Bfn_eqb b1 b2
  | fn_Z z1, fn_Z z2 => Zfn_eqb z1 z2
  | fn_R r1, fn_R r2 => Rfn_eqb r1 r2
  | _, _ => false
  end.

Definition fn_eqb_spec x y : BoolSpec (x = y) (x <> y) (fn_eqb x y).
Proof.
  unfold fn_eqb.
  destruct x, y; try (constructor; congruence).
  - destruct (Bfn_eqb_spec b b0); constructor; congruence.
  - destruct (Zfn_eqb_spec z z0); constructor; congruence.
  - destruct (Rfn_eqb_spec r r0); constructor; congruence.
Qed.

Definition expr_compatible (e1 e2 : expr) : bool :=
  match e1, e2 with
  | Datalog.var_expr _, Datalog.var_expr _ =>
      true
      (* XXX: need to handle alpha equivalence here? *)
  | Datalog.var_expr _, Datalog.fun_expr _ [] =>
      true
  | Datalog.fun_expr _ [], Datalog.var_expr _ =>
      true
  | Datalog.fun_expr f1 _, Datalog.fun_expr f2 _ => true (* For now we don't think about function equality *)
  | _, _ => false
  end.

End ATLDatalogParams.