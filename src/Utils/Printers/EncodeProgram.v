(* JSON encoders for the *source* Datalog AST (expr / clause / rule).

   Factored out of PrintPrograms.v so the encoders can be reused without pulling in the example
   programs or running any Redirects: PrintPrograms.v imports this to dump the bundled examples,
   and external tooling (the pipeline's emit driver) imports it to dump a program + its
   dependency-generator output. Decoupled from the broken Datalog.JSON submodule file; mirrors
   how PrintHardwareEncoding.v provides encoders for the compiled hardware AST. *)
From JSON Require Import Encode Printer.
From Datalog Require Import Datalog.
From Datalog.Util Require Export JSON.
From Stdlib Require Import List String.
Import ListNotations.

Section SourceEncoders.
Context {rel : relT} {var : exprvarT} {fn : fnT} {aggregator : aggregatorT}.
Context `{JEncode rel} `{JEncode var} `{JEncode fn} `{JEncode aggregator}.

Fixpoint encode_dexpr (e : Datalog.expr) : json :=
  match e with
  | expr.var v => JSON__Object [("var_expr", encode v)]
  | expr.app f args =>
      JSON__Object [("fun_expr", encode f);
                    ("args", JSON__Array (List.map encode_dexpr args))]
  end.
#[global] Instance JEncode__dexpr : JEncode (Datalog.expr) := encode_dexpr.

#[global] Instance JEncode__dclause : JEncode (Datalog.clause) := fun c =>
  JSON__Object [("clause_rel", encode c.(clause.rel));
                ("clause_args", encode c.(clause.args))].

#[global] Instance JEncode__drule : JEncode (Datalog.rule) := fun r =>
  match r with
  | rule.impl concls hyps =>
      JSON__Object [("normal_rule",
        JSON__Object [("concls", encode concls); ("hyps", encode hyps)])]
  | rule.agg cr agg hr =>
      JSON__Object [("agg_rule",
        JSON__Object [("concl_rel", encode cr); ("agg", encode agg); ("hyp_rel", encode hr)])]
  end.
End SourceEncoders.
