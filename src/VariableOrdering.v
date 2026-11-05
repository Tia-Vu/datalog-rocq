From Stdlib Require Import List Bool.
From Datalog Require Import Datalog List.

Import ListNotations.
Local Open Scope bool_scope.

Section VariableOrdering.
Context `{params : datalog_params}.

Definition variable_order (hyps : list clause) : list exprvar.
Admitted.

Definition order_ok (hyps : list clause) (order : list exprvar) :=
  NoDup order /\ same_set order (flat_map clause.vars hyps).

Lemma variable_order_ok hyps :
  order_ok hyps (variable_order hyps).
Proof. Admitted.

End VariableOrdering.
