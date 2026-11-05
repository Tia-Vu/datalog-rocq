(* Auto-generated from SouffleExamples/po2.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
From Stdlib Require Import ZArith.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope bool_scope.
Open Scope string_scope.
#[local] Instance string_fn : fnT := string.

(* {0: (2, 2), 1: (2, 2), 2: (2, 1), 3: (2, 0), 4: (2, 0), 5: (0, 0), 6: (1, 0), 7: (1, 1), 8: (1, 0), 9: (0, 2), 10: (1, 2), 11: (0, 0), 12: (0, 1), 13: (1, 1), 14: (1, 2), 15: (2, 1), 16: (0, 2), 17: (0, 1)} *)
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

(* A("1", i) :- Check(_anon0, b, c, d, e, _anon1), In(_anon2, b, c, d, e, _anon3, i). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "1" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "_anon1")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon2"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "_anon3"); (expr.var "i")] |}
    ]).

(* A("2", i) :- Check(a, _anon0, c, d, e, _anon1), In(a, _anon2, c, d, e, _anon3, i). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "2" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "_anon1")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon2"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "_anon3"); (expr.var "i")] |}
    ]).

(* A("3", i) :- Check(a, b, _anon0, _anon1, e, f), In(a, b, _anon2, _anon3, e, f, i). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "3" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("4", i) :- Check(_anon0, _anon1, c, d, _anon2, _anon3), In(_anon4, _anon5, c, d, _anon6, _anon7, i). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "4" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "c"); (expr.var "d"); (expr.var "_anon2"); (expr.var "_anon3")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon4"); (expr.var "_anon5"); (expr.var "c"); (expr.var "d"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "i")] |}
    ]).

(* A("5", i) :- Check(a, _anon0, _anon1, _anon2, _anon3, f), In(a, _anon4, _anon5, _anon6, _anon7, f, i). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "5" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("6", i) :- Check(_anon0, b, c, d, _anon1, f), In(_anon2, b, c, d, _anon3, f, i). *)
Definition rule_5 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "6" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon1"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon2"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon3"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("7", i) :- Check(_anon0, b, c, _anon1, e, f), In(_anon2, b, c, _anon3, e, f, i). *)
Definition rule_6 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "7" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "_anon1"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon2"); (expr.var "b"); (expr.var "c"); (expr.var "_anon3"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("8", i) :- Check(_anon0, b, _anon1, d, e, f), In(_anon2, b, _anon3, d, e, f, i). *)
Definition rule_7 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "8" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "_anon1"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon2"); (expr.var "b"); (expr.var "_anon3"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("9", i) :- Check(_anon0, _anon1, c, d, e, f), In(_anon2, _anon3, c, d, e, f, i). *)
Definition rule_8 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "9" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon2"); (expr.var "_anon3"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("10", i) :- Check(_anon0, b, c, d, _anon1, _anon2), In(_anon3, b, c, d, _anon4, _anon5, i). *)
Definition rule_9 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "10" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon1"); (expr.var "_anon2")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon3"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "i")] |}
    ]).

(* A("11", i) :- Check(_anon0, b, c, _anon1, _anon2, f), In(_anon3, b, c, _anon4, _anon5, f, i). *)
Definition rule_10 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "11" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon3"); (expr.var "b"); (expr.var "c"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("12", i) :- Check(_anon0, b, _anon1, _anon2, e, f), In(_anon3, b, _anon4, _anon5, e, f, i). *)
Definition rule_11 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "12" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon3"); (expr.var "b"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("13", i) :- Check(_anon0, _anon1, _anon2, d, e, f), In(_anon3, _anon4, _anon5, d, e, f, i). *)
Definition rule_12 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "13" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon3"); (expr.var "_anon4"); (expr.var "_anon5"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("14", i) :- Check(_anon0, b, c, _anon1, _anon2, _anon3), In(_anon4, b, c, _anon5, _anon6, _anon7, i). *)
Definition rule_13 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "14" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon4"); (expr.var "b"); (expr.var "c"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "i")] |}
    ]).

(* A("15", i) :- Check(_anon0, b, _anon1, _anon2, _anon3, f), In(_anon4, b, _anon5, _anon6, _anon7, f, i). *)
Definition rule_14 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "15" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon4"); (expr.var "b"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("16", i) :- Check(_anon0, _anon1, _anon2, _anon3, e, f), In(_anon4, _anon5, _anon6, _anon7, e, f, i). *)
Definition rule_15 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "16" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon4"); (expr.var "_anon5"); (expr.var "_anon6"); (expr.var "_anon7"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("17", i) :- Check(_anon0, b, c, d, e, f), In(_anon1, b, c, d, e, f, i). *)
Definition rule_16 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "17" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "_anon0"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "_anon1"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
    ]).

(* A("18", i) :- Check(a, b, c, d, e, f), In(a, b, c, d, e, f, i). *)
Definition rule_17 : rule :=
rule.impl ([
      {| clause.rel := "A"; clause.args := [(expr.app "18" []); (expr.var "i")] |}
    ]) ([
      {| clause.rel := "Check"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f")] |};
      {| clause.rel := "In"; clause.args := [(expr.var "a"); (expr.var "b"); (expr.var "c"); (expr.var "d"); (expr.var "e"); (expr.var "f"); (expr.var "i")] |}
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
   rule_14;
   rule_15;
   rule_16;
   rule_17].

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