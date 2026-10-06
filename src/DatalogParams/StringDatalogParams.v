From Datalog Require Export Datalog.
From Datalog.Util Require Export List.
From Stdlib Require Import String List.
From coqutil Require Import Datatypes.List.
From coqutil Require Export Eqb.   (* re-export so [string]'s [Eqb] reaches importers *)
From Datalog.Util Require Export Eqb.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.

(* The string instantiation of the datalog signature: relations, variables and function symbols
   are strings, aggregation is unused ([unit]), values are strings.  Registering each type as a
   typeclass instance lets every downstream [rule]/[clause]/... and every [eqb] be
   inferred -- no per-type aliases or equality definitions are needed ([string] has [Eqb] in
   coqutil, [unit] in [Datalog.Util.Eqb]). *)
#[export] Instance string_rel : relT := string.
#[export] Instance string_var : exprvarT := string.
#[export] Instance string_fn : fnT := string.
#[export] Instance string_aggregator : aggregatorT := unit.
#[export] Instance string_valueT : valueT := string.

(* Structural compatibility of two expressions for unification (NOT decidable equality):
   a variable matches anything; two applications match iff same head and compatible args. *)
Fixpoint expr_compatible (e1 e2 : expr) : bool :=
  match e1, e2 with
  | expr.var _, _ => true
  | _, expr.var _ => true
  | expr.app f1 args1, expr.app f2 args2 =>
      eqb f1 f2 && forallb2 expr_compatible args1 args2
  end.
