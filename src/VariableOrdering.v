From Stdlib Require Import List.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog List.

Import ListNotations.

Section VariableOrdering.
Context `{params : datalog_params}.

Definition variable_order (hyps : list clause) : list exprvar :=
  dedup (flat_map clause.vars hyps).

Definition order_ok (hyps : list clause) (order : list exprvar) :=
  NoDup order /\ same_set order (flat_map clause.vars hyps).

Lemma variable_order_ok hyps :
  order_ok hyps (variable_order hyps).
Proof. split; [apply NoDup_dedup | intros x; apply dedup_In]. Qed.

End VariableOrdering.
