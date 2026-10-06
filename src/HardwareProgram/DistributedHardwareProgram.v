From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram Topologies.Graph.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.
From Datalog.Util Require Import Eqb.

Section DistributedHardwareProgram.

Context {node_id : node_idT}.

Inductive destination :=
| DestEdge (e : node_id)
| DestTrie (t : trie_id).

End DistributedHardwareProgram.
Scheme Boolean Equality for destination.

Section DistributedHardwareProgram.

Context {node_id : node_idT}
        {node_id_eqb : Eqb node_id} {node_id_eqb_ok : Eqb_ok node_id_eqb}.

#[global] Instance destination_eqb : Eqb destination := destination_beq _ eqb.

#[global] Instance destination_eqb_ok : Eqb_ok destination_eqb.
Proof. eqb_ok. Qed.

(* The forwarding table routes each relation's facts to a set of destinations (edges/tries). *)
Context {forwarding_table : map.map rel_id (list destination)}.

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
