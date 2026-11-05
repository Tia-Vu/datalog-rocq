From Datalog Require Export Datalog.
From Datalog.Util Require Export List.
From Stdlib Require Import String List.
From coqutil Require Import Datatypes.List.
From coqutil Require Export Eqb.   (* re-export so [string]'s [Eqb] reaches importers *)
From Datalog.Util Require Export Eqb.
From DatalogRocq Require Import HardwareProgram.
Import ListNotations.
Open Scope bool_scope.

#[export] Instance string_rel : relT := string.
#[export] Instance string_var : exprvarT := string.
#[export] Existing Instance no_fns.
#[export] Existing Instance no_agg.
#[export] Instance string_valueT : valueT := string.

(* Structural compatibility of two expressions for unification (NOT decidable equality):
   a variable matches anything; two applications match iff same head and compatible args. *)
Section expr_compatible.
  Context {fn : fnT} {fn_eqb : Eqb fn}.

  Fixpoint expr_compatible (e1 e2 : @expr string_var fn) : bool :=
    match e1, e2 with
    | expr.var _, _ => true
    | _, expr.var _ => true
    | expr.app f1 args1, expr.app f2 args2 =>
        eqb f1 f2 && forallb2 expr_compatible args1 args2
    end.
End expr_compatible.
