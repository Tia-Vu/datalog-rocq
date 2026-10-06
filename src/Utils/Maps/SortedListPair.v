From coqutil Require Import sanity Map.Interface Map.SortedList.

Section ___.
Context {p1 p2 : Type}.
Context {p1_order : p1 -> p1 -> bool} {p1_order_spec : SortedList.parameters.strict_order p1_order}.
Context {p2_order : p2 -> p2 -> bool} {p2_order_spec : SortedList.parameters.strict_order p2_order}.

Definition pair_order (x y : p1 * p2) : bool :=
  let (x1, x2) := x in
  let (y1, y2) := y in
  if p1_order x1 y1 then true else if p1_order y1 x1 then false else p2_order x2 y2.

Lemma pair_order_irrefl: forall x y, pair_order (x, y) (x, y) = false.
Proof. intros. unfold pair_order.
        destruct p1_order_spec. rewrite (ltb_antirefl x).
        destruct p2_order_spec. auto.
Qed.

#[global] Instance pair_strict_order: SortedList.parameters.strict_order pair_order.
Proof. constructor.
  - intros [x y]. apply (pair_order_irrefl x y).
  - intros [x1 x2] [y1 y2] [z1 z2] Hxy Hyz. unfold pair_order in *.
    destruct p1_order_spec. destruct p2_order_spec.
    destruct (p1_order x1 z1) eqn:Hx1z1; auto;
    destruct (p1_order z1 x1) eqn:Hz1x1; auto;
    destruct (p1_order x1 y1) eqn:Hx1y1; auto;
    destruct (p1_order y1 z1) eqn:Hy1z1; auto.
    + pose proof (ltb_trans x1 y1 z1 Hx1y1 Hy1z1). rewrite H in Hx1z1. discriminate.
    + destruct (p1_order z1 y1) eqn:Hz1y1; auto.
      pose proof (ltb_total y1 z1 Hy1z1 Hz1y1). subst. rewrite Hx1y1 in Hx1z1. discriminate.
    + destruct (p1_order y1 x1) eqn:Hy1x1; auto.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst. rewrite Hy1z1 in Hx1z1. discriminate.
    + destruct (p1_order y1 x1) eqn:Hy1x1; auto. destruct (p1_order z1 y1) eqn:Hz1y1; auto.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst. pose proof (ltb_total y1 z1 Hy1z1 Hz1y1). subst.
      rewrite Hx1z1 in Hz1x1. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      pose proof (ltb_trans z1 y1 z1 Hx1y1 Hy1z1).
      pose proof (ltb_antirefl z1).
      rewrite H in H0. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      destruct (p1_order z1 y1) eqn:Hz1y1; auto; try discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      rewrite Hy1z1 in Hxy. discriminate.
    + pose proof (ltb_total x1 z1 Hx1z1 Hz1x1). subst.
      rewrite Hy1z1 in Hxy.
      rewrite Hx1y1 in Hyz.
      eauto.
    - intros [x1 x2] [y1 y2] Hxy Hyz. unfold pair_order in *.
      destruct p1_order_spec. destruct p2_order_spec.
      destruct (p1_order x1 y1) eqn:Hx1y1; auto; try discriminate.
      destruct (p1_order y1 x1) eqn:Hy1x1; auto; try discriminate.
      pose proof (ltb_total x1 y1 Hx1y1 Hy1x1). subst.
      pose proof (ltb_total0 x2 y2 Hxy Hyz). subst. auto.
Qed.

Definition Build_parameters T := SortedList.parameters.Build_parameters (p1 * p2) T pair_order.
#[global] Instance map T : map.map (p1 * p2) T := SortedList.map (Build_parameters T) pair_strict_order.
#[global] Instance ok T: map.ok (map T).
Proof. exact (@SortedList.map_ok (Build_parameters T) pair_strict_order). Qed.

End ___.
