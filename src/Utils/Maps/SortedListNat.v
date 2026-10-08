From coqutil Require Import sanity Map.Interface Map.SortedList.
From Stdlib Require Import ZArith Lia.

#[export] Instance Nat_strict_order: SortedList.parameters.strict_order Nat.ltb.
Proof. constructor.
  - intros x. apply Nat.ltb_irrefl.
  - intros x y z Hxy Hyz. rewrite Nat.ltb_lt. rewrite Nat.ltb_lt in Hxy. rewrite Nat.ltb_lt in Hyz. lia.
  - intros x y Hxy Hyz. Search ((_ <? _) = false). rewrite Nat.ltb_ge in Hxy. rewrite Nat.ltb_ge in Hyz. lia.
Qed.
