(* Auto-generated from SouffleExamples/po5.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Stdlib Require Import ZArith.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.
#[local] Instance string_fn : fnT := string.

(* ------------------------------------------------------------------ *)
(* Type parameters                                                      *)
(* Souffle relation/variable names are strings; we use string for       *)
(* rel, var, and fn.  aggregator = unit (aggregation not supported).    *)
(* ------------------------------------------------------------------ *)


(* Nullary function application = constant value *)
Definition const (c : string) : expr := expr.app c [].

(* ------------------------------------------------------------------ *)
(* Schema                                                               *)
(* ------------------------------------------------------------------ *)
(* .decl  Check(n1:number{->Z}, n2:number{->Z}, n3:number{->Z}, n4:number{->Z}, n5:number{->Z}, n6:number{->Z}) *)
(* .decl  In(n1:number{->Z}, n2:number{->Z}, n3:number{->Z}, n4:number{->Z}, n5:number{->Z}, n6:number{->Z}, in:number{->Z}) *)
(* .decl  A(l:number{->Z}, o:number{->Z}) *)

(* A("1", i) :- Check(a, b, c, d, e, f), In(a, b, c, d, e, f, i). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "1" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("2", i) :- Check(a, _anon0, _anon1, d, e, f), In(a, _anon2, _anon3, d, e, f, i). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "2" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("3", i) :- Check(a, b, _anon0, d, e, f), In(a, b, _anon1, d, e, f, i). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "3" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon1"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("4", i) :- Check(a, _anon0, _anon1, _anon2, e, f), In(a, _anon3, _anon4, _anon5, e, f, i). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "4" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon3"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("5", i) :- Check(a, b, _anon0, _anon1, _anon2, f), In(a, b, _anon3, _anon4, _anon5, f, i). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "5" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon3"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("6", i) :- Check(a, _anon0, _anon1, _anon2, _anon3, _anon4), In(a, _anon5, _anon6, _anon7, _anon8, _anon9, i). *)
Definition rule_5 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "6" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "_anon4")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "_anon8"); (expr.var "_anon9"); (expr.var "i")] |}
    ]).

(* A("7", i) :- Check(a, b, _anon0, d, e, f), In(a, b, _anon1, d, e, f, i). *)
Definition rule_6 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "7" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon1"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("8", i) :- Check(a, b, _anon0, _anon1, e, f), In(a, b, _anon2, _anon3, e, f, i). *)
Definition rule_7 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "8" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("9", i) :- Check(a, b, _anon0, _anon1, _anon2, f), In(a, b, _anon3, _anon4, _anon5, f, i). *)
Definition rule_8 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "9" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon3"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("10", i) :- Check(a, b, _anon0, _anon1, _anon2, _anon3), In(a, b, _anon4, _anon5, _anon6, _anon7, i). *)
Definition rule_9 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "10" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "i")] |}
    ]).

(* A("11", i) :- Check(a, b, c, _anon0, e, f), In(a, b, c, _anon1, e, f, i). *)
Definition rule_10 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "11" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "_anon0"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "_anon1"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("12", i) :- Check(a, _anon0, c, _anon1, _anon2, f), In(a, _anon3, c, _anon4, _anon5, f, i). *)
Definition rule_11 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "12" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "c"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon3"); (expr.var "c"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("13", i) :- Check(a, b, c, _anon0, _anon1, _anon2), In(a, b, c, _anon3, _anon4, _anon5, i). *)
Definition rule_12 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "13" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "_anon3"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "i")] |}
    ]).

(* A("14", i) :- Check(a, b, c, d, _anon0, f), In(a, b, c, d, _anon1, f, i). *)
Definition rule_13 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "14" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon0"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon1"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("15", i) :- Check(a, _anon0, c, d, _anon1, _anon2), In(a, _anon3, c, d, _anon4, _anon5, i). *)
Definition rule_14 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "15" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "c"); (expr.var "d"); (expr.var "_anon1"); (expr.var "_anon2")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon3"); (expr.var "c"); (expr.var "d"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "i")] |}
    ]).

Definition program : list rule :=
  [rule_0;
   rule_1;
   rule_2;
   rule_3;
   rule_4;
   rule_5;
   rule_6;
   rule_7;
   rule_8;
   rule_9;
   rule_10;
   rule_11;
   rule_12;
   rule_13;
   rule_14].

Definition computed_program := Eval compute in program.
Print computed_program.


(* Temp fix, may use typeclasses later *)
Definition get_program_dependencies (p : list rule) :=
  DependencyGenerator.get_program_dependencies (expr_compatible := expr_compatible)
    p.

Definition get_rule_dependencies (p : list rule) (r : rule) :=
  DependencyGenerator.get_rule_dependencies (expr_compatible := expr_compatible)
    p r.

Definition get_program_dependencies_flat (p : list rule) :=
  DependencyGenerator.get_program_dependencies_flat
    (expr_compatible := expr_compatible)
    p.

Compute get_program_dependencies computed_program.
Compute get_rule_dependencies
        computed_program
        rule_1.

Compute get_program_dependencies_flat computed_program.