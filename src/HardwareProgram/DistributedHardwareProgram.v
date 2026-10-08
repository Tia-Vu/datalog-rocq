From Stdlib Require Import List String Bool ZArith.
From DatalogRocq Require Import HardwareProgram Topologies.Graph.
From coqutil Require Import Datatypes.List Map.Interface Map.Properties Eqb.
From Datalog.Util Require Import Map Eqb.

#[export] Abbreviation channel_id := nat (only parsing).

Module fwd_from.
  Variant fwd_from {node_id : node_idT} :=
    | input
    | self
    | node (_ : node_id) (_ : channel_id).
  Scheme Boolean Equality for fwd_from.
  Section eqb.
    Context {node_id : node_idT} {nid_eqb : Eqb node_id} {nid_eqb_ok : Eqb_ok nid_eqb}.
    #[export] Instance eqb {node_id : node_idT} `{Eqb node_id} : Eqb fwd_from := fwd_from_beq _ eqb.
    #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.
  End eqb.
End fwd_from. Export (hints) fwd_from. Abbreviation fwd_from := fwd_from.fwd_from.
#[export] Register Scheme fwd_from.eqb as beq for fwd_from.fwd_from.

Module fwd_to.
  Variant fwd_to {node_id : node_idT} :=
    | output
    | self
    | node (_ : node_id) (_ : channel_id).
  Scheme Boolean Equality for fwd_to.
  Section eqb.
    Context {node_id : node_idT} {nid_eqb : Eqb node_id} {nid_eqb_ok : Eqb_ok nid_eqb}.
    #[export] Instance eqb {node_id : node_idT} `{Eqb node_id} : Eqb fwd_to := fwd_to_beq _ eqb.
    #[export] Instance eqb_ok : Eqb_ok eqb. Proof. eqb_ok. Qed.
  End eqb.
End fwd_to. Export (hints) fwd_to. Abbreviation fwd_to := fwd_to.fwd_to.
#[export] Register Scheme fwd_to.eqb as beq for fwd_to.fwd_to.

Section DistributedHardwareProgram.
  Context {node_id : node_idT}.
  Context {_fwd_tbl : map.map (rel_id * fwd_from) (list fwd_to)}.

  Definition forwarding_table := partial_map (rel_id * fwd_from) (list fwd_to).

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
