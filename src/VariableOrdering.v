From Stdlib Require Import List.
From coqutil Require Import Datatypes.List.
From Datalog Require Import Datalog List Default.

Import ListNotations.

Section VariableOrdering.
Context `{params : datalog_params}.

(*TODO do something cleverer here*)
Definition variable_order (hyps : list clause) : list exprvar :=
  dedup (flat_map clause.vars hyps).

Definition order_ok (hyps : list clause) (order : list exprvar) :=
  NoDup order /\ same_set order (flat_map clause.vars hyps).

Lemma variable_order_ok hyps :
  order_ok hyps (variable_order hyps).
Proof. split; [apply NoDup_dedup | intros x; apply dedup_In]. Qed.

Definition order_variables (r : rule) :=
  match r with
  | rule.impl concls hyps =>
      let order := variable_order hyps in
      let lookup := fun v => unwrap_or_default (index_of v order) in
      rule.impl
        (map (clause_varmap lookup) concls)
        (map (clause_varmap lookup) hyps)
  | rule.agg concl a src => rule.agg concl a src
  end.
End VariableOrdering.
