From coqutil Require Import sanity Map.Interface Map.SortedList.

Module strict_order_map.
  Section ___.
    Context {A : Type} {A_order : A -> A -> bool} {A_order_spec : SortedList.parameters.strict_order A_order}.

    Definition Build_parameters T := SortedList.parameters.Build_parameters A T A_order.
    #[export] Instance map T : map.map A T := SortedList.map (Build_parameters T) A_order_spec.
    #[export] Instance ok T : map.ok (map T).
    Proof. exact (@SortedList.map_ok (Build_parameters T) A_order_spec). Qed.

  End ___.
End strict_order_map. Export (hints) strict_order_map.
