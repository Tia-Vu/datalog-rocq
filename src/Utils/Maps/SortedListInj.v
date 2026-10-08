From coqutil Require Import sanity Map.Interface Map.SortedList.

Section ___.
Context {A B : Type} (f : A -> B) (f_inj : forall x y, f x = f y -> x = y).
Context {B_order : B -> B -> bool} {B_order_spec : SortedList.parameters.strict_order B_order}.

Definition inj_order (x y : A) : bool := B_order (f x) (f y).

Lemma inj_strict_order : SortedList.parameters.strict_order inj_order.
Proof.
  destruct B_order_spec as [Hirr Htrans Htot]. constructor; unfold inj_order.
  - intros k. apply Hirr.
  - intros k1 k2 k3. apply Htrans.
  - intros k1 k2 H1 H2. apply f_inj, Htot; assumption.
Qed.

End ___.
