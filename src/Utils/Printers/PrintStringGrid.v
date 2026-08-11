From JSON Require Import Encode Printer.
From Stdlib Require Import String List ZArith.
From coqutil Require Import Map.Interface Result.
From DatalogRocq Require Import DistributedDatalogToHardwareCompiler PrintHardwareEncoding.
From DatalogRocq Require Import StringDatalogParams GridTopology GridGraph SortedListNat StringGridCompiler.
From DatalogRocq Require Import FamilyCompiler BasicProgramCompiler GraphCompiler CsdaCompiler CspaCompiler Po1Compiler Po2Compiler Po3Compiler Po4Compiler Po5Compiler PointstoCompiler RanpoCompiler ReachCompiler TcCompiler TransCompiler TriangleCompiler X9Compiler Unitprop1Compiler.

Notation node_id := GridGraph.Node.

Definition nat_to_string (n : nat) : string :=
  NilZero.string_of_uint (Nat.to_uint n).

Fixpoint coords_to_string (l : list nat) : string :=
  match l with
  | [] => ""
  | [x] => nat_to_string x
  | x :: rest => nat_to_string x ++ ", " ++ coords_to_string rest
  end.

Definition node_id_to_string (n : GridGraph.Node) : string :=
  "(" ++ coords_to_string n ++ ")".

Instance JEncode__grid_node_id : JEncode GridGraph.Node :=
  fun n => JSON__String (node_id_to_string n).

Redirect "json_examples/compiled_family_program" Eval vm_compute in (to_string (encode compiled_family)).
Redirect "json_examples/compiled_basic_program" Eval vm_compute in (to_string (encode compiled_basic_program)).
Redirect "json_examples/compiled_graph_program" Eval vm_compute in (to_string (encode compiled_graph)).
Redirect "json_examples/compiled_csda_program" Eval vm_compute in (to_string (encode compiled_csda)).
Redirect "json_examples/compiled_cspa_program" Eval vm_compute in (to_string (encode compiled_cspa)).
Redirect "json_examples/compiled_po1_program" Eval vm_compute in (to_string (encode compiled_po1)).
Redirect "json_examples/compiled_po2_program" Eval vm_compute in (to_string (encode compiled_po2)).
Redirect "json_examples/compiled_po3_program" Eval vm_compute in (to_string (encode compiled_po3)).
Redirect "json_examples/compiled_po4_program" Eval vm_compute in (to_string (encode compiled_po4)).
Redirect "json_examples/compiled_po5_program" Eval vm_compute in (to_string (encode compiled_po5)).
Redirect "json_examples/compiled_pointsto_program" Eval vm_compute in (to_string (encode compiled_pointsto)).
Redirect "json_examples/compiled_ranpo_program" Eval vm_compute in (to_string (encode compiled_ranpo)).
Redirect "json_examples/compiled_reach_program" Eval vm_compute in (to_string (encode compiled_reach)).
Redirect "json_examples/compiled_tc_program" Eval vm_compute in (to_string (encode compiled_tc)).
Redirect "json_examples/compiled_trans_program" Eval vm_compute in (to_string (encode compiled_trans)).
Redirect "json_examples/compiled_triangle_program" Eval vm_compute in (to_string (encode compiled_triangle)).
Redirect "json_examples/compiled_x9_program" Eval vm_compute in (to_string (encode compiled_x9)).
Redirect "json_examples/compiled_unitprop1_program" Eval vm_compute in (to_string (encode compiled_unitprop1)).
