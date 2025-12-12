From coqutil Require Import Option.

Lemma pair_eqb_spec {A B} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool)
      (specA : forall x y, BoolSpec (x = y) (x <> y) (eqbA x y))
      (specB : forall x y, BoolSpec (x = y) (x <> y) (eqbB x y))
      (p1 p2 : A * B) :
  BoolSpec (p1 = p2) (p1 <> p2)
           (let (a1,b1) := p1 in let (a2,b2) := p2 in eqbA a1 a2 && eqbB b1 b2).
Proof.
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