(* This takes a datalog program, and for every rule, it generates the rules that it might depend on *)
From Datalog Require Import Datalog.
From Stdlib Require Import List.
From Stdlib Require Import String.
Import ListNotations.


(* Then, it will try to generate a layout for the program which can be fed into gurobi *)

Definition rel := string.
Definition var := string.
Definition fn := string.
Definition aggregator := unit.
Definition T := nat.  (* semantic domain for interpretation *)
Definition rule := Datalog.rule rel var fn aggregator.
Definition program := list rule.


(* For every rule we want the transitive closure of its dependencies. Given a program, 
   we want to be able to get all the rules that could possibly generate conclusions that
   would be used in hypotheses *)

Definition get_rule_concls_rels (r : rule) : list rel :=
  map (fun fact => Datalog.fact_R fact) (Datalog.rule_concls r).


Definition get_rule_hyps_rels (r : rule) : list rel :=
  map (fun fact => Datalog.fact_R fact) (Datalog.rule_hyps r).


(* We want to get every single rule that generates conclusions that the hypotheses might depend on *)
Definition get_directly_dependent_rules (p : program) (r : rule) : program :=
  filter (fun r' => 
            let conc_rels := get_rule_concls_rels r' in
            let hyp_rels := get_rule_hyps_rels r in
            existsb (fun rel => existsb (String.eqb rel) conc_rels) hyp_rels)
         p.

Compute (get_directly_dependent_rules [] ({| Datalog.rule_hyps := []; Datalog.rule_concls := [] |})).

