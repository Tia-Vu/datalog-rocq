(* ATL to Datalog broken so we're skipping for now *)

(* From Stdlib Require Import List Bool ZArith.Znat Lia.
From DatalogRocq Require Import DistributedDatalog GridGraph DependencyGenerator ATLDatalogParams Matmul GridLayout.
From Datalog Require Import Datalog CompilerExamples ATLToDatalog.
From coqutil Require Import Map.Interface Map.Properties Map.Solver.
Import ListNotations.

Section SmallExample.
  Definition rel := ATLDatalogParams.rel.
  Definition var := ATLDatalogParams.var.
  Definition fn := ATLDatalogParams.fn.
  Definition aggregator := ATLDatalogParams.aggregator.
  Definition T := ATLDatalogParams.T.
  Definition rule := Datalog.rule (exprvar := var).

  Context {context : map.map var T}.
  Context {context_ok : map.ok context}.
  Context {sig : signature fn aggregator T}.

  Definition dims : list nat := [3; 3].

  Definition program : list rule := datalog_matmul. 

  Print datalog_matmul.

  Definition indexed_layout : list (Node * list nat) := 
    [([2;0], [0]); 
    ([0;2], [1]); 
    ([0;0], [2]); 
    ([2;2], [3]); 
    ([1;2], [4]); 
    ([1;1], [5]); 
    ([1;0], [6]); 
    ([2;1], [7]); 
    ([0;1], [8])].

  Definition datalog_matmul_3x3 := @mk_dataflow_network rel var fn aggregator T dims indexed_layout program.
  Definition rule_eqb := @DependencyGenerator.rule_eqb rel var fn aggregator var_eqb rel_eqb fn_eqb aggregator_eqb.
  Definition rule_eqb_spec := @DependencyGenerator.rule_eqb_spec rel var fn aggregator var_eqb var_eqb_spec rel_eqb rel_eqb_spec fn_eqb fn_eqb_spec aggregator_eqb aggregator_eqb_spec.

  Definition check_layout := @GridLayout.check_layout rel var fn aggregator rule_eqb.
  Definition mk_layout := @GridLayout.mk_layout_from_indexed_layout rel var fn aggregator.

  (* Should be True! Our layout passes the checker *)
  Compute check_layout dims (mk_layout_from_indexed_layout dims indexed_layout program) program.

  Definition soundness := @GridLayout.soundness rel var fn aggregator T sig context rule_eqb rule_eqb_spec.

  Theorem soundness_check :
    forall f,
      network_prog_impl_fact
      (mk_dataflow_network dims indexed_layout program) f ->
      prog_impl_fact program f.
  Proof.
    intros.
    eapply soundness; eauto.
    vm_compute. reflexivity.
  Qed.

End SmallExample. *)

(* ============================================================================ *)
(*  Non-ATL example: the (string) family program laid out on a 3x3 grid.        *)
(*  Replaces the ATL/matmul example above, which is blocked on the broken       *)
(*  ATLToDatalog submodule file.                                                *)
(* ============================================================================ *)

From Stdlib Require Import List Bool String.
From Datalog Require Import Datalog.
From DatalogRocq Require Import DistributedDatalog GridGraph
  GridLayout StringDatalogParams Family.
From coqutil Require Import Map.Interface.
Import ListNotations.
Import StringDatalogParams.

Section FamilyExample.
  (* The semantics (interpretation) parameters are kept abstract; only
     semantics/context/value_set are needed (the layout/forwarding facts are structural). *)
  Context {context : map.map string string} {context_ok : map.ok context}.
  Context {semantics : datalog_semantics string unit string}.
  Context {value_set : map.map (list string) unit} {value_set_ok : map.ok value_set}.

  Definition dims : list nat := [3; 3].
  Definition program : list rule := family_program.

  (* Assign family's 8 rules to 8 of the 9 grid nodes (last node idle). *)
  Definition indexed_layout : list (Node * list nat) :=
    [ ([0;0], [0]); ([0;1], [1]); ([0;2], [2]); ([1;0], [3]);
      ([1;1], [4]); ([1;2], [5]); ([2;0], [6]); ([2;1], [7]); ([2;2], []) ].

  Definition family_3x3 := GridLayout.mk_dataflow_network dims indexed_layout program.

  (* The layout passes the checker (should compute to [true]); [rule]'s [Eqb] is inferred. *)
  Compute GridLayout.good_layoutb (GridGraph.all_nodes_h dims)
            (GridLayout.mk_layout_from_indexed_layout dims indexed_layout program) program.

  (* The grid network built from this layout is well-formed. *)
  Theorem family_3x3_good_network :
    DistributedDatalog.good_network family_3x3 program.
  Proof.
    apply GridLayout.good_network. vm_compute. reflexivity.
  Qed.

  (* Soundness: every fact the distributed grid network derives is derivable by the
     reference (single-machine) family program from an empty input database. *)
  Theorem family_3x3_soundness :
    forall f,
      DistributedDatalog.network_prog_impl_fact family_3x3 f ->
      program.interp {| program.rules := program; program.meta_rules := [] |} (fun _ => False) f.
  Proof.
    intros f Hnet.
    destruct family_3x3_good_network as [_ [Hgl _]].
    apply (DistributedDatalog.soundness family_3x3 program (fun _ => False)); auto.
  Qed.

End FamilyExample.
