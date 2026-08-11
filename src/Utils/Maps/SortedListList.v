From coqutil Require Import sanity Map.Interface Map.SortedList.
From Stdlib Require Import List.
Import ListNotations.

Section ___.
Context {A : Type}.
Context {A_order : A -> A -> bool} {A_order_spec : SortedList.parameters.strict_order A_order}.

Fixpoint list_order (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x1 :: xs1, x2 :: xs2 =>
      if A_order x1 x2 then true
      else if A_order x2 x1 then false
      else list_order xs1 xs2
  end.


Lemma list_order_irrefl: forall l, list_order l l = false.
Proof. induction l; auto. simpl. destruct A_order_spec.
       destruct (A_order a a) eqn:Haa; auto.
       pose proof (ltb_antirefl a). eauto.
Qed.

#[global] Instance list_strict_order: SortedList.parameters.strict_order list_order.
Proof.
  constructor.
  - intros l. apply (list_order_irrefl l).
  - intros l1. induction l1; intros l2 l3; intros.
    + destruct l2; destruct l3; auto.
    + destruct l2; destruct l3; destruct A_order_spec; auto; simpl in *; try discriminate.
      destruct (A_order a a1) eqn:Haa1; auto; try discriminate;
      destruct (A_order a1 a) eqn:Haa1'; auto; try discriminate;
      destruct (A_order a a0) eqn:Haa0; auto; try discriminate;
      destruct (A_order a0 a1) eqn:Ha0a1; auto; try discriminate.
      * pose proof (ltb_trans a a0 a1 Haa0 Ha0a1). rewrite H1 in Haa1. discriminate.
      * destruct (A_order a1 a0) eqn: Ha1a0; auto; try discriminate.
        pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst. rewrite Haa0 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto.
        pose proof (ltb_total a a0 Haa0 Ha0a). subst. rewrite Ha0a1 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto.
        destruct (A_order a1 a0) eqn:Ha1a0; auto.
        pose proof (ltb_total a a0 Haa0 Ha0a). subst. pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst.
        rewrite <- Haa1'. auto.
      * pose proof (ltb_trans a a0 a1 Haa0 Ha0a1). rewrite H1 in Haa1. discriminate.
      * destruct (A_order a1 a0) eqn: Ha1a0; auto; try discriminate.
        pose proof (ltb_total a0 a1 Ha0a1 Ha1a0). subst. rewrite Haa0 in Haa1. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto; try discriminate.
        pose proof (ltb_total a a1 Haa1 Haa1'). subst. rewrite Ha0a1 in Ha0a. discriminate.
      * destruct (A_order a0 a) eqn:Ha0a; auto; try discriminate.
        destruct (A_order a1 a0) eqn:Ha1a0; auto; try discriminate.
        eapply IHl1; eauto.
  - induction k1; destruct k2; simpl in *; intros; auto; try discriminate.
    destruct A_order_spec.
    destruct (A_order a a0) eqn:Haa0; auto; try discriminate;
    destruct (A_order a0 a) eqn:Haa0'; auto; try discriminate.
    pose proof (ltb_total a a0 Haa0 Haa0'). subst.
    specialize (IHk1 k2 H H0). subst. auto.
Qed.

Definition Build_parameters T := SortedList.parameters.Build_parameters (list A) T list_order.
#[global] Instance map T : map.map (list A) T := SortedList.map (Build_parameters T) list_strict_order.
#[global] Instance ok T: map.ok (map T).
Proof. exact (@SortedList.map_ok (Build_parameters T) list_strict_order). Qed.
End ___.
