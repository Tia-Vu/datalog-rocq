Definition node_idT := Type.
Existing Class node_idT.
#[global] Typeclasses Transparent node_idT.

Section Graph.
  
  Context {Node : Type}.

  Record Graph := {
    nodes : Node -> Prop;
    edge : Node -> Node -> Prop
  }.

  Definition good_graph (g : Graph) := 
   forall n1 n2, edge g n1 n2 -> nodes g n1 /\ nodes g n2.

  Inductive path (g : Graph) : Node -> Node -> Prop :=
  | path_nil n :
      g.(nodes) n ->
      path g n n 
  | path_cons n1 n2 n3 :
      g.(edge) n1 n2 ->
      path g n2 n3 ->
      path g n1 n3.

  Definition strongly_connected (g : Graph) : Prop :=
    forall n1 n2, g.(nodes) n1 -> g.(nodes) n2 -> path g n1 n2.
    
End Graph.