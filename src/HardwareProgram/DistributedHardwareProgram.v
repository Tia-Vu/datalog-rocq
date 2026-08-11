From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.

Section DistributedHardwareProgram.

Context {node_id : Type}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

(* The forwarding table routes each relation's facts to a set of destinations (edges). *)
Context {forwarding_table : map.map (rel_id * node_id) (list node_id)}.

(* A compiled node's program: its trie-join rules ([nprogram]), the tries they read ([ntries]),
   and the forwarding table ([nforwarding]).  This is the per-node piece of the *distributed*
   hardware program; the compiler ([DistributedDatalogToHardwareCompiler]) is what produces it. *)
Record node_info := {
  nid : node_id;
  nprogram : hardware_program;
  nforwarding : forwarding_table;
  ntries : list trie;
}.

End DistributedHardwareProgram.
