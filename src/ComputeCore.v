From Stdlib Require Import Lists.ListSet.
From Stdlib Require Import Arith.Peano_dec.

Definition core_id := nat.

Definition core_eqb (c1 c2: core_id) : bool :=
  Nat.eqb c1 c2.

Definition eq_core_dec (c1 c2: core_id) := eq_nat_dec c1 c2.

Definition core_set := set core_id.

Definition core_set_add := set_add eq_core_dec.
Definition core_set_remove := set_remove eq_core_dec.
Definition core_set_mem := set_mem eq_core_dec.
Definition core_set_union := set_union eq_core_dec.
Definition core_set_inter := set_inter eq_core_dec.
Definition core_set_diff := set_diff eq_core_dec.
Definition empty_core_set := empty_set core_id.

Notation "x =c y" := (core_eqb x y) (at level 70).

