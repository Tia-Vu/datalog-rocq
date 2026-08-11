From JSON Require Import Encode Printer.
From Stdlib Require Import String List ZArith.
From coqutil Require Import Map.Interface Result.
From DatalogRocq Require Import HardwareProgram DistributedHardwareProgram.

(* Generic JSON encoders for the compiled hardware-program AST.

   Everything from [trie] downward is purely numeric, so its encoding is fixed here once
   and for all.  The *only* topology-specific choice is how a [node_id] prints, which this
   file takes as a parameter ([JEncode node_id]) together with the forwarding-table map. *)

Section PrintHardwareEncoding.

Context {node_id : Type}.
Context `{JEncode node_id}.

Context {forwarding_table : map.map (rel_id * node_id) (list node_id)}.

Notation node_info := (@DistributedHardwareProgram.node_info node_id forwarding_table).

#[global] Instance JEncode__pair A B `{JEncode A} `{JEncode B} : JEncode (A * B) :=
  fun '(a, b) => JSON__Array [encode a; encode b].

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

#[global] Instance JEncode_forwarding_table : JEncode forwarding_table :=
  fun m => encode (map.fold (fun acc k v => (k, v) :: acc) [] m).

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

#[global] Instance JEncode__sum {A B} `{JEncode A} `{JEncode B} : JEncode (A + B) :=
  fun ab =>
  match ab with
  | inl a => JSON__Object [("inl", encode a)]
  | inr b => JSON__Object [("inr", encode b)]
  end.

End PrintHardwareEncoding.
