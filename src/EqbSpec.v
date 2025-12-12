From coqutil Require Import Option.

Definition pair_eqb {A B} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool)
           (p1 p2 : A * B) : bool :=
  let (a1, b1) := p1 in
  let (a2, b2) := p2 in
  eqbA a1 a2 && eqbB b1 b2.

Lemma pair_eqb_spec {A B} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool)
      (specA : forall x y, BoolSpec (x = y) (x <> y) (eqbA x y))
      (specB : forall x y, BoolSpec (x = y) (x <> y) (eqbB x y))
      (p1 p2 : A * B) :
  BoolSpec (p1 = p2) (p1 <> p2) (pair_eqb eqbA eqbB p1 p2).
Proof.
  unfold pair_eqb.
  destruct p1 as [a1 b1], p2 as [a2 b2].
  destruct (specA a1 a2); destruct (specB b1 b2); constructor; congruence.
Qed.

Lemma option_eqb_spec {A} (eqbA : A -> A -> bool)
      (specA : forall x y, BoolSpec (x = y) (x <> y) (eqbA x y))
      (o1 o2 : option A) :
  BoolSpec (o1 = o2) (o1 <> o2)
            (match o1, o2 with
              | None, None => true
              | Some a1, Some a2 => eqbA a1 a2
              | _, _ => false
              end).
Proof.
  destruct o1, o2.
  - destruct (specA a a0); constructor; congruence.
  - constructor; congruence.
  - constructor; congruence.
  - constructor; reflexivity.
Qed.