From Stdlib Require Import List Arith.
Import ListNotations.

Record uf : Type := {
  parent : list nat;
  rank   : list nat
}.

(* nth with a sane default: if out-of-bounds, return index *)
Definition get (l : list nat) (i : nat) : nat :=
  nth i l i.

Fixpoint update (l : list nat) (i v : nat) : list nat :=
  match l, i with
  | [], _ => []
  | _ :: xs, 0 => v :: xs
  | x :: xs, S n => x :: update xs n v
  end.

Definition create (n : nat) : uf :=
  {| parent := seq 0 n;    (* seq 0 n = [0;1;...;n-1] *)
     rank   := repeat 0 n |}.

Fixpoint find_aux (u : uf) (x : nat) (fuel : nat) : nat * uf :=
  match fuel with
  | 0 => (x, u)  (* out of fuel *)
  | S k' =>
      let p := get (parent u) x in
      if Nat.eqb p x then (x, u)
      else
        let (root, u') := find_aux u p k' in
        let new_parent := update (parent u') x root in
        (root, {| parent := new_parent; rank := rank u' |})
  end.

Definition find (u : uf) (x : nat) : nat * uf :=
  find_aux u x (length (parent u)).  (* we should never have a chain longer than the number of nodes *)

(* union using find *)
Definition union (u : uf) (x y : nat) : uf :=
  let '(rx, u1) := find u x in
  let '(ry, u2) := find u1 y in
  match Nat.compare rx ry with
  | Gt =>
      {| parent := update (parent u2) ry rx;
         rank := rank u2 |}
  | Lt =>
      {| parent := update (parent u2) rx ry;
         rank := rank u2 |}
  | Eq => u2
  end.
