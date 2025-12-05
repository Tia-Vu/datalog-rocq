From StdLib Require Import List Arith Lia.
Import ListNotations.

Record Graph (Node : Type) := {
  nodes : Node -> Prop;
  edge  : Node -> Node -> Prop
}.

Section GridGraph.

  Variable dims : list nat.
  Definition Node := Vector.t nat (length dims).

  (* All nodes are allowed (infinite grid for now) *)
  Definition is_node (_ : Node) : Prop := True.

  (* Simple adjacency: differs by +1 on exactly one coordinate *)
  Definition is_edge (u v : Node) : Prop :=
    exists i (Hi : i < length dims),
      Vector.nth v (Fin.of_nat_lt Hi)
      =
      S (Vector.nth u (Fin.of_nat_lt Hi)).

  (* The actual graph *)
  Definition GridGraph : Graph Node :=
    {|
      nodes := is_node;
      edge  := is_edge
    |}.

End GridGraph.



