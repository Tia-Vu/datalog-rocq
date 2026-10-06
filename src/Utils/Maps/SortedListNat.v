From coqutil Require Import sanity Map.Interface Map.SortedList.
From Stdlib Require Import ZArith Lia.

#[global] Instance Nat_strict_order: SortedList.parameters.strict_order Nat.ltb.
Proof. constructor.
  - intros x. apply Nat.ltb_irrefl.
  - intros x y z Hxy Hyz. rewrite Nat.ltb_lt. rewrite Nat.ltb_lt in Hxy. rewrite Nat.ltb_lt in Hyz. lia.
  - intros x y Hxy Hyz. Search ((_ <? _) = false). rewrite Nat.ltb_ge in Hxy. rewrite Nat.ltb_ge in Hyz. lia.
Qed.

Definition Build_parameters T := SortedList.parameters.Build_parameters nat T Nat.ltb.
#[global] Instance map T : map.map nat T := SortedList.map (Build_parameters T) Nat_strict_order.
#[global] Instance ok T: map.ok (map T).
Proof. exact (@SortedList.map_ok (Build_parameters T) Nat_strict_order). Qed.
