From JSON Require Import Encode Printer.
From Stdlib Require Import String List ZArith.
From coqutil Require Import Map.Interface Result.
From Datalog.Util Require Export JSON.
From DatalogRocq Require Import Topologies.Graph HardwareProgram DistributedHardwareProgram.

(* Generic JSON encoders for the compiled hardware-program AST.

   Everything from [trie] downward is purely numeric, so its encoding is fixed here once
   and for all.  The *only* topology-specific choice is how a [node_id] prints, which this
   file takes as a parameter ([JEncode node_id]) together with the forwarding-table map. *)

Section PrintHardwareEncoding.

Context {node_id : node_idT}.
Context `{JEncode node_id}.
Context {map_rel_id_fwd_from_list_fwd_to : map.map (rel_id * fwd_from) (list fwd_to)}.

#[global] Instance JEncode__join : JEncode join :=
  fun j =>
    JSON__Object [("tries", encode j.(tries));
                ("trie_levels", encode j.(trie_levels));
                ("clauses", encode j.(clauses))].

#[global] Instance JEncode__join_output : JEncode join_output :=
  fun jo =>
    JSON__Object [("output_rel", encode jo.(output_rel));
                ("output_var_indices", encode jo.(output_var_indices))].

#[global] Instance JEncode_hardware_rule : JEncode hardware_rule :=
  fun hr =>
    JSON__Object [("hhyps", encode hr.(hhyps));
                ("hconcls", encode hr.(hconcls))].

#[global] Instance JEncode__fwd_from : JEncode fwd_from := fun src =>
  match src with
  | fwd_from.input => JSON__String "input"
  | fwd_from.self => JSON__String "self"
  | fwd_from.node n ch => JSON__Object [("node", JSON__Object [("id", encode n); ("channel", encode ch)])]
  end.

#[global] Instance JEncode__fwd_to : JEncode fwd_to := fun dst =>
  match dst with
  | fwd_to.output => JSON__String "output"
  | fwd_to.self => JSON__String "self"
  | fwd_to.node n ch => JSON__Object [("node", JSON__Object [("id", encode n); ("channel", encode ch)])]
  end.

#[global] Instance JEncode__trie : JEncode trie :=
  fun t =>
    JSON__Object [("tid", encode t.(tid));
                ("trel", encode t.(trel));
                ("tperm", encode t.(tperm))].

#[global] Instance JEncode__node_info : JEncode node_info :=
  fun ni =>
    JSON__Object [("nid", encode ni.(nid));
                ("nprogram", encode ni.(nprogram));
                ("nforwarding", encode ni.(nforwarding));
                ("ntries", encode ni.(ntries))].

#[global] Instance JEncode__Result {A} `{JEncode A} : JEncode (result A) :=
  fun r =>
  match r with
  | Success a => encode a
  | Failure _ => JSON__String "Failed to compile"
  end.

End PrintHardwareEncoding.
