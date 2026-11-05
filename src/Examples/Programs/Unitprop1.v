(* Auto-generated from ../Benchmarks/SouffleExamples/unitprop1.dl by souffle_to_rocq *)
From Stdlib Require Import Strings.String List Bool.
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
(* .type Val <: symbol  {-> string} *)
(* .decl  forced_true(x:symbol{->string}) *)
(* .decl  forced_false(x:symbol{->string}) *)
(* .decl  sat(c:symbol{->string}) *)
(* .decl  contradiction(x:symbol{->string}) *)
(* .decl  clause0(lit_v0:Val{->string}) *)
(* .decl  clause1(lit_nv0:Val{->string}, lit_v1:Val{->string}) *)
(* .decl  clause2(lit_nv0:Val{->string}, lit_v2:Val{->string}) *)
(* .decl  clause3(lit_nv1:Val{->string}, lit_nv2:Val{->string}, lit_v3:Val{->string}) *)
(* .decl  clause4(lit_nv1:Val{->string}, lit_v4:Val{->string}) *)
(* .decl  clause5(lit_nv2:Val{->string}, lit_nv3:Val{->string}, lit_v5:Val{->string}) *)
(* .decl  clause6(lit_nv3:Val{->string}, lit_nv4:Val{->string}, lit_v6:Val{->string}) *)
(* .decl  clause7(lit_nv5:Val{->string}, lit_nv6:Val{->string}, lit_nv7:Val{->string}) *)
(* .decl  clause8(lit_nv5:Val{->string}, lit_v8:Val{->string}) *)
(* .decl  clause9(lit_nv6:Val{->string}, lit_v9:Val{->string}) *)
(* .decl  clause10(lit_nv8:Val{->string}, lit_v10:Val{->string}) *)
(* .decl  clause11(lit_nv9:Val{->string}, lit_v11:Val{->string}) *)
(* .decl  clause12(lit_nv10:Val{->string}, lit_nv11:Val{->string}, lit_nv12:Val{->string}) *)
(* .decl  clause13(lit_nv11:Val{->string}, lit_nv12:Val{->string}, lit_v13:Val{->string}) *)
(* .decl  clause14(lit_nv10:Val{->string}, lit_nv13:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause15(lit_v7:Val{->string}, lit_v12:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause16(lit_nv4:Val{->string}, lit_nv8:Val{->string}, lit_v13:Val{->string}, lit_v14:Val{->string}) *)
(* .decl  clause17(lit_nv13:Val{->string}, lit_nv14:Val{->string}, lit_v0:Val{->string}, lit_v1:Val{->string}) *)
(* .decl  clause18(lit_v2:Val{->string}, lit_v4:Val{->string}, lit_v6:Val{->string}, lit_v8:Val{->string}) *)
(* .decl  clause19(lit_nv0:Val{->string}, lit_nv1:Val{->string}, lit_nv2:Val{->string}, lit_v3:Val{->string}, lit_v5:Val{->string}) *)
(* .decl  unsat(r:symbol{->string}) *)
(* .output forced_true *)
(* .output forced_false *)
(* .output sat *)
(* .output unsat *)
(* .output contradiction *)

(* clause0("unknown"). *)
Definition rule_0 : rule :=
rule.impl ([
      {| clause.rel := "clause0"; clause.args := [(expr.app "unknown" [])] |}
    ]) ([]).

(* clause0("true") :- forced_true("v0"). *)
Definition rule_1 : rule :=
rule.impl ([
      {| clause.rel := "clause0"; clause.args := [(expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause0("false") :- forced_false("v0"). *)
Definition rule_2 : rule :=
rule.impl ([
      {| clause.rel := "clause0"; clause.args := [(expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* forced_true("v0"). *)
Definition rule_3 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]) ([]).

(* sat("C0") :- clause0("true"). *)
Definition rule_4 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C0" [])] |}
    ]) ([
      {| clause.rel := "clause0"; clause.args := [(expr.app "true" [])] |}
    ]).

(* clause1("unknown", "unknown"). *)
Definition rule_5 : rule :=
rule.impl ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause1("true", B) :- clause1(_anon0, B), forced_false("v0"). *)
Definition rule_6 : rule :=
rule.impl ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause1("false", B) :- clause1(_anon0, B), forced_true("v0"). *)
Definition rule_7 : rule :=
rule.impl ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause1(A, "true") :- clause1(A, _anon0), forced_true("v1"). *)
Definition rule_8 : rule :=
rule.impl ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause1(A, "false") :- clause1(A, _anon0), forced_false("v1"). *)
Definition rule_9 : rule :=
rule.impl ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* sat("C1") :- clause1("true", _anon0). *)
Definition rule_10 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C1" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C1") :- clause1(_anon0, "true"). *)
Definition rule_11 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C1" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v1") :- clause1("false", "unknown"). *)
Definition rule_12 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause1("unknown", "false"). *)
Definition rule_13 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]) ([
      {| clause.rel := "clause1"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause2("unknown", "unknown"). *)
Definition rule_14 : rule :=
rule.impl ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause2("true", B) :- clause2(_anon0, B), forced_false("v0"). *)
Definition rule_15 : rule :=
rule.impl ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause2("false", B) :- clause2(_anon0, B), forced_true("v0"). *)
Definition rule_16 : rule :=
rule.impl ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause2(A, "true") :- clause2(A, _anon0), forced_true("v2"). *)
Definition rule_17 : rule :=
rule.impl ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause2(A, "false") :- clause2(A, _anon0), forced_false("v2"). *)
Definition rule_18 : rule :=
rule.impl ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* sat("C2") :- clause2("true", _anon0). *)
Definition rule_19 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C2" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C2") :- clause2(_anon0, "true"). *)
Definition rule_20 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C2" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v2") :- clause2("false", "unknown"). *)
Definition rule_21 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause2("unknown", "false"). *)
Definition rule_22 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]) ([
      {| clause.rel := "clause2"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause3("unknown", "unknown", "unknown"). *)
Definition rule_23 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause3("true", B, C) :- clause3(_anon0, B, C), forced_false("v1"). *)
Definition rule_24 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause3("false", B, C) :- clause3(_anon0, B, C), forced_true("v1"). *)
Definition rule_25 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause3(A, "true", C) :- clause3(A, _anon0, C), forced_false("v2"). *)
Definition rule_26 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause3(A, "false", C) :- clause3(A, _anon0, C), forced_true("v2"). *)
Definition rule_27 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause3(A, B, "true") :- clause3(A, B, _anon0), forced_true("v3"). *)
Definition rule_28 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause3(A, B, "false") :- clause3(A, B, _anon0), forced_false("v3"). *)
Definition rule_29 : rule :=
rule.impl ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* sat("C3") :- clause3("true", _anon0, _anon1). *)
Definition rule_30 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C3" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C3") :- clause3(_anon0, "true", _anon1). *)
Definition rule_31 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C3" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C3") :- clause3(_anon0, _anon1, "true"). *)
Definition rule_32 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C3" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v3") :- clause3("false", "false", "unknown"). *)
Definition rule_33 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v1") :- clause3("unknown", "false", "false"). *)
Definition rule_34 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v2") :- clause3("false", "unknown", "false"). *)
Definition rule_35 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]) ([
      {| clause.rel := "clause3"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause4("unknown", "unknown"). *)
Definition rule_36 : rule :=
rule.impl ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause4("true", B) :- clause4(_anon0, B), forced_false("v1"). *)
Definition rule_37 : rule :=
rule.impl ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause4("false", B) :- clause4(_anon0, B), forced_true("v1"). *)
Definition rule_38 : rule :=
rule.impl ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause4(A, "true") :- clause4(A, _anon0), forced_true("v4"). *)
Definition rule_39 : rule :=
rule.impl ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause4(A, "false") :- clause4(A, _anon0), forced_false("v4"). *)
Definition rule_40 : rule :=
rule.impl ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* sat("C4") :- clause4("true", _anon0). *)
Definition rule_41 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C4" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C4") :- clause4(_anon0, "true"). *)
Definition rule_42 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C4" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v4") :- clause4("false", "unknown"). *)
Definition rule_43 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v1") :- clause4("unknown", "false"). *)
Definition rule_44 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]) ([
      {| clause.rel := "clause4"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause5("unknown", "unknown", "unknown"). *)
Definition rule_45 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause5("true", B, C) :- clause5(_anon0, B, C), forced_false("v2"). *)
Definition rule_46 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause5("false", B, C) :- clause5(_anon0, B, C), forced_true("v2"). *)
Definition rule_47 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause5(A, "true", C) :- clause5(A, _anon0, C), forced_false("v3"). *)
Definition rule_48 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause5(A, "false", C) :- clause5(A, _anon0, C), forced_true("v3"). *)
Definition rule_49 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause5(A, B, "true") :- clause5(A, B, _anon0), forced_true("v5"). *)
Definition rule_50 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause5(A, B, "false") :- clause5(A, B, _anon0), forced_false("v5"). *)
Definition rule_51 : rule :=
rule.impl ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* sat("C5") :- clause5("true", _anon0, _anon1). *)
Definition rule_52 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C5" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C5") :- clause5(_anon0, "true", _anon1). *)
Definition rule_53 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C5" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C5") :- clause5(_anon0, _anon1, "true"). *)
Definition rule_54 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C5" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v5") :- clause5("false", "false", "unknown"). *)
Definition rule_55 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v2") :- clause5("unknown", "false", "false"). *)
Definition rule_56 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v3") :- clause5("false", "unknown", "false"). *)
Definition rule_57 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]) ([
      {| clause.rel := "clause5"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause6("unknown", "unknown", "unknown"). *)
Definition rule_58 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause6("true", B, C) :- clause6(_anon0, B, C), forced_false("v3"). *)
Definition rule_59 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause6("false", B, C) :- clause6(_anon0, B, C), forced_true("v3"). *)
Definition rule_60 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause6(A, "true", C) :- clause6(A, _anon0, C), forced_false("v4"). *)
Definition rule_61 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause6(A, "false", C) :- clause6(A, _anon0, C), forced_true("v4"). *)
Definition rule_62 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause6(A, B, "true") :- clause6(A, B, _anon0), forced_true("v6"). *)
Definition rule_63 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause6(A, B, "false") :- clause6(A, B, _anon0), forced_false("v6"). *)
Definition rule_64 : rule :=
rule.impl ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* sat("C6") :- clause6("true", _anon0, _anon1). *)
Definition rule_65 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C6" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C6") :- clause6(_anon0, "true", _anon1). *)
Definition rule_66 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C6" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C6") :- clause6(_anon0, _anon1, "true"). *)
Definition rule_67 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C6" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v6") :- clause6("false", "false", "unknown"). *)
Definition rule_68 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v3") :- clause6("unknown", "false", "false"). *)
Definition rule_69 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v4") :- clause6("false", "unknown", "false"). *)
Definition rule_70 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]) ([
      {| clause.rel := "clause6"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause7("unknown", "unknown", "unknown"). *)
Definition rule_71 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause7("true", B, C) :- clause7(_anon0, B, C), forced_false("v5"). *)
Definition rule_72 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause7("false", B, C) :- clause7(_anon0, B, C), forced_true("v5"). *)
Definition rule_73 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause7(A, "true", C) :- clause7(A, _anon0, C), forced_false("v6"). *)
Definition rule_74 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause7(A, "false", C) :- clause7(A, _anon0, C), forced_true("v6"). *)
Definition rule_75 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause7(A, B, "true") :- clause7(A, B, _anon0), forced_false("v7"). *)
Definition rule_76 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v7" [])] |}
    ]).

(* clause7(A, B, "false") :- clause7(A, B, _anon0), forced_true("v7"). *)
Definition rule_77 : rule :=
rule.impl ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v7" [])] |}
    ]).

(* sat("C7") :- clause7("true", _anon0, _anon1). *)
Definition rule_78 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C7" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C7") :- clause7(_anon0, "true", _anon1). *)
Definition rule_79 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C7" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C7") :- clause7(_anon0, _anon1, "true"). *)
Definition rule_80 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C7" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_false("v7") :- clause7("false", "false", "unknown"). *)
Definition rule_81 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v7" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v5") :- clause7("unknown", "false", "false"). *)
Definition rule_82 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v6") :- clause7("false", "unknown", "false"). *)
Definition rule_83 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]) ([
      {| clause.rel := "clause7"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause8("unknown", "unknown"). *)
Definition rule_84 : rule :=
rule.impl ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause8("true", B) :- clause8(_anon0, B), forced_false("v5"). *)
Definition rule_85 : rule :=
rule.impl ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause8("false", B) :- clause8(_anon0, B), forced_true("v5"). *)
Definition rule_86 : rule :=
rule.impl ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause8(A, "true") :- clause8(A, _anon0), forced_true("v8"). *)
Definition rule_87 : rule :=
rule.impl ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause8(A, "false") :- clause8(A, _anon0), forced_false("v8"). *)
Definition rule_88 : rule :=
rule.impl ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* sat("C8") :- clause8("true", _anon0). *)
Definition rule_89 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C8" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C8") :- clause8(_anon0, "true"). *)
Definition rule_90 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C8" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v8") :- clause8("false", "unknown"). *)
Definition rule_91 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v5") :- clause8("unknown", "false"). *)
Definition rule_92 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]) ([
      {| clause.rel := "clause8"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause9("unknown", "unknown"). *)
Definition rule_93 : rule :=
rule.impl ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause9("true", B) :- clause9(_anon0, B), forced_false("v6"). *)
Definition rule_94 : rule :=
rule.impl ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause9("false", B) :- clause9(_anon0, B), forced_true("v6"). *)
Definition rule_95 : rule :=
rule.impl ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause9(A, "true") :- clause9(A, _anon0), forced_true("v9"). *)
Definition rule_96 : rule :=
rule.impl ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v9" [])] |}
    ]).

(* clause9(A, "false") :- clause9(A, _anon0), forced_false("v9"). *)
Definition rule_97 : rule :=
rule.impl ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v9" [])] |}
    ]).

(* sat("C9") :- clause9("true", _anon0). *)
Definition rule_98 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C9" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C9") :- clause9(_anon0, "true"). *)
Definition rule_99 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C9" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v9") :- clause9("false", "unknown"). *)
Definition rule_100 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v9" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v6") :- clause9("unknown", "false"). *)
Definition rule_101 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]) ([
      {| clause.rel := "clause9"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause10("unknown", "unknown"). *)
Definition rule_102 : rule :=
rule.impl ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause10("true", B) :- clause10(_anon0, B), forced_false("v8"). *)
Definition rule_103 : rule :=
rule.impl ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause10("false", B) :- clause10(_anon0, B), forced_true("v8"). *)
Definition rule_104 : rule :=
rule.impl ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause10(A, "true") :- clause10(A, _anon0), forced_true("v10"). *)
Definition rule_105 : rule :=
rule.impl ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* clause10(A, "false") :- clause10(A, _anon0), forced_false("v10"). *)
Definition rule_106 : rule :=
rule.impl ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* sat("C10") :- clause10("true", _anon0). *)
Definition rule_107 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C10" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C10") :- clause10(_anon0, "true"). *)
Definition rule_108 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C10" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v10") :- clause10("false", "unknown"). *)
Definition rule_109 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v10" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v8") :- clause10("unknown", "false"). *)
Definition rule_110 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]) ([
      {| clause.rel := "clause10"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause11("unknown", "unknown"). *)
Definition rule_111 : rule :=
rule.impl ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause11("true", B) :- clause11(_anon0, B), forced_false("v9"). *)
Definition rule_112 : rule :=
rule.impl ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "true" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v9" [])] |}
    ]).

(* clause11("false", B) :- clause11(_anon0, B), forced_true("v9"). *)
Definition rule_113 : rule :=
rule.impl ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "false" []); (expr.var "B")] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "_anon0"); (expr.var "B")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v9" [])] |}
    ]).

(* clause11(A, "true") :- clause11(A, _anon0), forced_true("v11"). *)
Definition rule_114 : rule :=
rule.impl ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "A"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* clause11(A, "false") :- clause11(A, _anon0), forced_false("v11"). *)
Definition rule_115 : rule :=
rule.impl ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "A"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "A"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* sat("C11") :- clause11("true", _anon0). *)
Definition rule_116 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C11" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "true" []); (expr.var "_anon0")] |}
    ]).

(* sat("C11") :- clause11(_anon0, "true"). *)
Definition rule_117 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C11" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.var "_anon0"); (expr.app "true" [])] |}
    ]).

(* forced_true("v11") :- clause11("false", "unknown"). *)
Definition rule_118 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v11" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v9") :- clause11("unknown", "false"). *)
Definition rule_119 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v9" [])] |}
    ]) ([
      {| clause.rel := "clause11"; clause.args := [(expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause12("unknown", "unknown", "unknown"). *)
Definition rule_120 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause12("true", B, C) :- clause12(_anon0, B, C), forced_false("v10"). *)
Definition rule_121 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* clause12("false", B, C) :- clause12(_anon0, B, C), forced_true("v10"). *)
Definition rule_122 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* clause12(A, "true", C) :- clause12(A, _anon0, C), forced_false("v11"). *)
Definition rule_123 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* clause12(A, "false", C) :- clause12(A, _anon0, C), forced_true("v11"). *)
Definition rule_124 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* clause12(A, B, "true") :- clause12(A, B, _anon0), forced_false("v12"). *)
Definition rule_125 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* clause12(A, B, "false") :- clause12(A, B, _anon0), forced_true("v12"). *)
Definition rule_126 : rule :=
rule.impl ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* sat("C12") :- clause12("true", _anon0, _anon1). *)
Definition rule_127 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C12" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C12") :- clause12(_anon0, "true", _anon1). *)
Definition rule_128 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C12" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C12") :- clause12(_anon0, _anon1, "true"). *)
Definition rule_129 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C12" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_false("v12") :- clause12("false", "false", "unknown"). *)
Definition rule_130 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v12" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v10") :- clause12("unknown", "false", "false"). *)
Definition rule_131 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v10" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v11") :- clause12("false", "unknown", "false"). *)
Definition rule_132 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v11" [])] |}
    ]) ([
      {| clause.rel := "clause12"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause13("unknown", "unknown", "unknown"). *)
Definition rule_133 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause13("true", B, C) :- clause13(_anon0, B, C), forced_false("v11"). *)
Definition rule_134 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* clause13("false", B, C) :- clause13(_anon0, B, C), forced_true("v11"). *)
Definition rule_135 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v11" [])] |}
    ]).

(* clause13(A, "true", C) :- clause13(A, _anon0, C), forced_false("v12"). *)
Definition rule_136 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* clause13(A, "false", C) :- clause13(A, _anon0, C), forced_true("v12"). *)
Definition rule_137 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* clause13(A, B, "true") :- clause13(A, B, _anon0), forced_true("v13"). *)
Definition rule_138 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause13(A, B, "false") :- clause13(A, B, _anon0), forced_false("v13"). *)
Definition rule_139 : rule :=
rule.impl ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* sat("C13") :- clause13("true", _anon0, _anon1). *)
Definition rule_140 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C13" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C13") :- clause13(_anon0, "true", _anon1). *)
Definition rule_141 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C13" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C13") :- clause13(_anon0, _anon1, "true"). *)
Definition rule_142 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C13" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v13") :- clause13("false", "false", "unknown"). *)
Definition rule_143 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v11") :- clause13("unknown", "false", "false"). *)
Definition rule_144 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v11" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v12") :- clause13("false", "unknown", "false"). *)
Definition rule_145 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v12" [])] |}
    ]) ([
      {| clause.rel := "clause13"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause14("unknown", "unknown", "unknown"). *)
Definition rule_146 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause14("true", B, C) :- clause14(_anon0, B, C), forced_false("v10"). *)
Definition rule_147 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* clause14("false", B, C) :- clause14(_anon0, B, C), forced_true("v10"). *)
Definition rule_148 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v10" [])] |}
    ]).

(* clause14(A, "true", C) :- clause14(A, _anon0, C), forced_false("v13"). *)
Definition rule_149 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause14(A, "false", C) :- clause14(A, _anon0, C), forced_true("v13"). *)
Definition rule_150 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause14(A, B, "true") :- clause14(A, B, _anon0), forced_true("v14"). *)
Definition rule_151 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* clause14(A, B, "false") :- clause14(A, B, _anon0), forced_false("v14"). *)
Definition rule_152 : rule :=
rule.impl ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* sat("C14") :- clause14("true", _anon0, _anon1). *)
Definition rule_153 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C14" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C14") :- clause14(_anon0, "true", _anon1). *)
Definition rule_154 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C14" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C14") :- clause14(_anon0, _anon1, "true"). *)
Definition rule_155 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C14" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v14") :- clause14("false", "false", "unknown"). *)
Definition rule_156 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v10") :- clause14("unknown", "false", "false"). *)
Definition rule_157 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v10" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v13") :- clause14("false", "unknown", "false"). *)
Definition rule_158 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]) ([
      {| clause.rel := "clause14"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* clause15("unknown", "unknown", "unknown"). *)
Definition rule_159 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause15("true", B, C) :- clause15(_anon0, B, C), forced_true("v7"). *)
Definition rule_160 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v7" [])] |}
    ]).

(* clause15("false", B, C) :- clause15(_anon0, B, C), forced_false("v7"). *)
Definition rule_161 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v7" [])] |}
    ]).

(* clause15(A, "true", C) :- clause15(A, _anon0, C), forced_true("v12"). *)
Definition rule_162 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* clause15(A, "false", C) :- clause15(A, _anon0, C), forced_false("v12"). *)
Definition rule_163 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C")] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v12" [])] |}
    ]).

(* clause15(A, B, "true") :- clause15(A, B, _anon0), forced_true("v14"). *)
Definition rule_164 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* clause15(A, B, "false") :- clause15(A, B, _anon0), forced_false("v14"). *)
Definition rule_165 : rule :=
rule.impl ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* sat("C15") :- clause15("true", _anon0, _anon1). *)
Definition rule_166 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C15" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1")] |}
    ]).

(* sat("C15") :- clause15(_anon0, "true", _anon1). *)
Definition rule_167 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C15" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1")] |}
    ]).

(* sat("C15") :- clause15(_anon0, _anon1, "true"). *)
Definition rule_168 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C15" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" [])] |}
    ]).

(* forced_true("v7") :- clause15("unknown", "false", "false"). *)
Definition rule_169 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v7" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v12") :- clause15("false", "unknown", "false"). *)
Definition rule_170 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v12" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v14") :- clause15("false", "false", "unknown"). *)
Definition rule_171 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]) ([
      {| clause.rel := "clause15"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* clause16("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_172 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause16("true", B, C, D) :- clause16(_anon0, B, C, D), forced_false("v4"). *)
Definition rule_173 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause16("false", B, C, D) :- clause16(_anon0, B, C, D), forced_true("v4"). *)
Definition rule_174 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause16(A, "true", C, D) :- clause16(A, _anon0, C, D), forced_false("v8"). *)
Definition rule_175 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause16(A, "false", C, D) :- clause16(A, _anon0, C, D), forced_true("v8"). *)
Definition rule_176 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause16(A, B, "true", D) :- clause16(A, B, _anon0, D), forced_true("v13"). *)
Definition rule_177 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause16(A, B, "false", D) :- clause16(A, B, _anon0, D), forced_false("v13"). *)
Definition rule_178 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause16(A, B, C, "true") :- clause16(A, B, C, _anon0), forced_true("v14"). *)
Definition rule_179 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* clause16(A, B, C, "false") :- clause16(A, B, C, _anon0), forced_false("v14"). *)
Definition rule_180 : rule :=
rule.impl ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* sat("C16") :- clause16("true", _anon0, _anon1, _anon2). *)
Definition rule_181 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C16" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, "true", _anon1, _anon2). *)
Definition rule_182 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C16" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, _anon1, "true", _anon2). *)
Definition rule_183 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C16" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" []); (expr.var "_anon2")] |}
    ]).

(* sat("C16") :- clause16(_anon0, _anon1, _anon2, "true"). *)
Definition rule_184 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C16" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.app "true" [])] |}
    ]).

(* forced_true("v13") :- clause16("false", "false", "unknown", "false"). *)
Definition rule_185 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v14") :- clause16("false", "false", "false", "unknown"). *)
Definition rule_186 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v4") :- clause16("unknown", "false", "false", "false"). *)
Definition rule_187 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v8") :- clause16("false", "unknown", "false", "false"). *)
Definition rule_188 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]) ([
      {| clause.rel := "clause16"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* clause17("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_189 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause17("true", B, C, D) :- clause17(_anon0, B, C, D), forced_false("v13"). *)
Definition rule_190 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause17("false", B, C, D) :- clause17(_anon0, B, C, D), forced_true("v13"). *)
Definition rule_191 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v13" [])] |}
    ]).

(* clause17(A, "true", C, D) :- clause17(A, _anon0, C, D), forced_false("v14"). *)
Definition rule_192 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* clause17(A, "false", C, D) :- clause17(A, _anon0, C, D), forced_true("v14"). *)
Definition rule_193 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v14" [])] |}
    ]).

(* clause17(A, B, "true", D) :- clause17(A, B, _anon0, D), forced_true("v0"). *)
Definition rule_194 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause17(A, B, "false", D) :- clause17(A, B, _anon0, D), forced_false("v0"). *)
Definition rule_195 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause17(A, B, C, "true") :- clause17(A, B, C, _anon0), forced_true("v1"). *)
Definition rule_196 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause17(A, B, C, "false") :- clause17(A, B, C, _anon0), forced_false("v1"). *)
Definition rule_197 : rule :=
rule.impl ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* sat("C17") :- clause17("true", _anon0, _anon1, _anon2). *)
Definition rule_198 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C17" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, "true", _anon1, _anon2). *)
Definition rule_199 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C17" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, _anon1, "true", _anon2). *)
Definition rule_200 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C17" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" []); (expr.var "_anon2")] |}
    ]).

(* sat("C17") :- clause17(_anon0, _anon1, _anon2, "true"). *)
Definition rule_201 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C17" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.app "true" [])] |}
    ]).

(* forced_true("v0") :- clause17("false", "false", "unknown", "false"). *)
Definition rule_202 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v1") :- clause17("false", "false", "false", "unknown"). *)
Definition rule_203 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v13") :- clause17("unknown", "false", "false", "false"). *)
Definition rule_204 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v13" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v14") :- clause17("false", "unknown", "false", "false"). *)
Definition rule_205 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v14" [])] |}
    ]) ([
      {| clause.rel := "clause17"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* clause18("unknown", "unknown", "unknown", "unknown"). *)
Definition rule_206 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause18("true", B, C, D) :- clause18(_anon0, B, C, D), forced_true("v2"). *)
Definition rule_207 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause18("false", B, C, D) :- clause18(_anon0, B, C, D), forced_false("v2"). *)
Definition rule_208 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause18(A, "true", C, D) :- clause18(A, _anon0, C, D), forced_true("v4"). *)
Definition rule_209 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause18(A, "false", C, D) :- clause18(A, _anon0, C, D), forced_false("v4"). *)
Definition rule_210 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C"); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v4" [])] |}
    ]).

(* clause18(A, B, "true", D) :- clause18(A, B, _anon0, D), forced_true("v6"). *)
Definition rule_211 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause18(A, B, "false", D) :- clause18(A, B, _anon0, D), forced_false("v6"). *)
Definition rule_212 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" []); (expr.var "D")] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v6" [])] |}
    ]).

(* clause18(A, B, C, "true") :- clause18(A, B, C, _anon0), forced_true("v8"). *)
Definition rule_213 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* clause18(A, B, C, "false") :- clause18(A, B, C, _anon0), forced_false("v8"). *)
Definition rule_214 : rule :=
rule.impl ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v8" [])] |}
    ]).

(* sat("C18") :- clause18("true", _anon0, _anon1, _anon2). *)
Definition rule_215 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C18" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, "true", _anon1, _anon2). *)
Definition rule_216 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C18" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1"); (expr.var "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, _anon1, "true", _anon2). *)
Definition rule_217 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C18" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" []); (expr.var "_anon2")] |}
    ]).

(* sat("C18") :- clause18(_anon0, _anon1, _anon2, "true"). *)
Definition rule_218 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C18" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.app "true" [])] |}
    ]).

(* forced_true("v2") :- clause18("unknown", "false", "false", "false"). *)
Definition rule_219 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v4") :- clause18("false", "unknown", "false", "false"). *)
Definition rule_220 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v4" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v6") :- clause18("false", "false", "unknown", "false"). *)
Definition rule_221 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v6" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v8") :- clause18("false", "false", "false", "unknown"). *)
Definition rule_222 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v8" [])] |}
    ]) ([
      {| clause.rel := "clause18"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* clause19("unknown", "unknown", "unknown", "unknown", "unknown"). *)
Definition rule_223 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" []); (expr.app "unknown" [])] |}
    ]) ([]).

(* clause19("true", B, C, D, E) :- clause19(_anon0, B, C, D, E), forced_false("v0"). *)
Definition rule_224 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "true" []); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause19("false", B, C, D, E) :- clause19(_anon0, B, C, D, E), forced_true("v0"). *)
Definition rule_225 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "false" []); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v0" [])] |}
    ]).

(* clause19(A, "true", C, D, E) :- clause19(A, _anon0, C, D, E), forced_false("v1"). *)
Definition rule_226 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.app "true" []); (expr.var "C"); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause19(A, "false", C, D, E) :- clause19(A, _anon0, C, D, E), forced_true("v1"). *)
Definition rule_227 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.app "false" []); (expr.var "C"); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "_anon0"); (expr.var "C"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v1" [])] |}
    ]).

(* clause19(A, B, "true", D, E) :- clause19(A, B, _anon0, D, E), forced_false("v2"). *)
Definition rule_228 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "true" []); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause19(A, B, "false", D, E) :- clause19(A, B, _anon0, D, E), forced_true("v2"). *)
Definition rule_229 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.app "false" []); (expr.var "D"); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "_anon0"); (expr.var "D"); (expr.var "E")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v2" [])] |}
    ]).

(* clause19(A, B, C, "true", E) :- clause19(A, B, C, _anon0, E), forced_true("v3"). *)
Definition rule_230 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "true" []); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0"); (expr.var "E")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause19(A, B, C, "false", E) :- clause19(A, B, C, _anon0, E), forced_false("v3"). *)
Definition rule_231 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.app "false" []); (expr.var "E")] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "_anon0"); (expr.var "E")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v3" [])] |}
    ]).

(* clause19(A, B, C, D, "true") :- clause19(A, B, C, D, _anon0), forced_true("v5"). *)
Definition rule_232 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.app "true" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* clause19(A, B, C, D, "false") :- clause19(A, B, C, D, _anon0), forced_false("v5"). *)
Definition rule_233 : rule :=
rule.impl ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.app "false" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "A"); (expr.var "B"); (expr.var "C"); (expr.var "D"); (expr.var "_anon0")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v5" [])] |}
    ]).

(* sat("C19") :- clause19("true", _anon0, _anon1, _anon2, _anon3). *)
Definition rule_234 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C19" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "true" []); (expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, "true", _anon1, _anon2, _anon3). *)
Definition rule_235 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C19" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.app "true" []); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, "true", _anon2, _anon3). *)
Definition rule_236 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C19" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.app "true" []); (expr.var "_anon2"); (expr.var "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, _anon2, "true", _anon3). *)
Definition rule_237 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C19" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.app "true" []); (expr.var "_anon3")] |}
    ]).

(* sat("C19") :- clause19(_anon0, _anon1, _anon2, _anon3, "true"). *)
Definition rule_238 : rule :=
rule.impl ([
      {| clause.rel := "sat"; clause.args := [(expr.app "C19" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.var "_anon0"); (expr.var "_anon1"); (expr.var "_anon2"); (expr.var "_anon3"); (expr.app "true" [])] |}
    ]).

(* forced_true("v3") :- clause19("false", "false", "false", "unknown", "false"). *)
Definition rule_239 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v3" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "unknown" []); (expr.app "false" [])] |}
    ]).

(* forced_true("v5") :- clause19("false", "false", "false", "false", "unknown"). *)
Definition rule_240 : rule :=
rule.impl ([
      {| clause.rel := "forced_true"; clause.args := [(expr.app "v5" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "unknown" [])] |}
    ]).

(* forced_false("v0") :- clause19("unknown", "false", "false", "false", "false"). *)
Definition rule_241 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v0" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "unknown" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v1") :- clause19("false", "unknown", "false", "false", "false"). *)
Definition rule_242 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v1" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "false" []); (expr.app "unknown" []); (expr.app "false" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* forced_false("v2") :- clause19("false", "false", "unknown", "false", "false"). *)
Definition rule_243 : rule :=
rule.impl ([
      {| clause.rel := "forced_false"; clause.args := [(expr.app "v2" [])] |}
    ]) ([
      {| clause.rel := "clause19"; clause.args := [(expr.app "false" []); (expr.app "false" []); (expr.app "unknown" []); (expr.app "false" []); (expr.app "false" [])] |}
    ]).

(* contradiction(X) :- forced_true(X), forced_false(X). *)
Definition rule_244 : rule :=
rule.impl ([
      {| clause.rel := "contradiction"; clause.args := [(expr.var "X")] |}
    ]) ([
      {| clause.rel := "forced_true"; clause.args := [(expr.var "X")] |};
      {| clause.rel := "forced_false"; clause.args := [(expr.var "X")] |}
    ]).

(* unsat("UNSAT") :- contradiction(_anon0). *)
Definition rule_245 : rule :=
rule.impl ([
      {| clause.rel := "unsat"; clause.args := [(expr.app "UNSAT" [])] |}
    ]) ([
      {| clause.rel := "contradiction"; clause.args := [(expr.var "_anon0")] |}
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
   rule_17;
   rule_18;
   rule_19;
   rule_20;
   rule_21;
   rule_22;
   rule_23;
   rule_24;
   rule_25;
   rule_26;
   rule_27;
   rule_28;
   rule_29;
   rule_30;
   rule_31;
   rule_32;
   rule_33;
   rule_34;
   rule_35;
   rule_36;
   rule_37;
   rule_38;
   rule_39;
   rule_40;
   rule_41;
   rule_42;
   rule_43;
   rule_44;
   rule_45;
   rule_46;
   rule_47;
   rule_48;
   rule_49;
   rule_50;
   rule_51;
   rule_52;
   rule_53;
   rule_54;
   rule_55;
   rule_56;
   rule_57;
   rule_58;
   rule_59;
   rule_60;
   rule_61;
   rule_62;
   rule_63;
   rule_64;
   rule_65;
   rule_66;
   rule_67;
   rule_68;
   rule_69;
   rule_70;
   rule_71;
   rule_72;
   rule_73;
   rule_74;
   rule_75;
   rule_76;
   rule_77;
   rule_78;
   rule_79;
   rule_80;
   rule_81;
   rule_82;
   rule_83;
   rule_84;
   rule_85;
   rule_86;
   rule_87;
   rule_88;
   rule_89;
   rule_90;
   rule_91;
   rule_92;
   rule_93;
   rule_94;
   rule_95;
   rule_96;
   rule_97;
   rule_98;
   rule_99;
   rule_100;
   rule_101;
   rule_102;
   rule_103;
   rule_104;
   rule_105;
   rule_106;
   rule_107;
   rule_108;
   rule_109;
   rule_110;
   rule_111;
   rule_112;
   rule_113;
   rule_114;
   rule_115;
   rule_116;
   rule_117;
   rule_118;
   rule_119;
   rule_120;
   rule_121;
   rule_122;
   rule_123;
   rule_124;
   rule_125;
   rule_126;
   rule_127;
   rule_128;
   rule_129;
   rule_130;
   rule_131;
   rule_132;
   rule_133;
   rule_134;
   rule_135;
   rule_136;
   rule_137;
   rule_138;
   rule_139;
   rule_140;
   rule_141;
   rule_142;
   rule_143;
   rule_144;
   rule_145;
   rule_146;
   rule_147;
   rule_148;
   rule_149;
   rule_150;
   rule_151;
   rule_152;
   rule_153;
   rule_154;
   rule_155;
   rule_156;
   rule_157;
   rule_158;
   rule_159;
   rule_160;
   rule_161;
   rule_162;
   rule_163;
   rule_164;
   rule_165;
   rule_166;
   rule_167;
   rule_168;
   rule_169;
   rule_170;
   rule_171;
   rule_172;
   rule_173;
   rule_174;
   rule_175;
   rule_176;
   rule_177;
   rule_178;
   rule_179;
   rule_180;
   rule_181;
   rule_182;
   rule_183;
   rule_184;
   rule_185;
   rule_186;
   rule_187;
   rule_188;
   rule_189;
   rule_190;
   rule_191;
   rule_192;
   rule_193;
   rule_194;
   rule_195;
   rule_196;
   rule_197;
   rule_198;
   rule_199;
   rule_200;
   rule_201;
   rule_202;
   rule_203;
   rule_204;
   rule_205;
   rule_206;
   rule_207;
   rule_208;
   rule_209;
   rule_210;
   rule_211;
   rule_212;
   rule_213;
   rule_214;
   rule_215;
   rule_216;
   rule_217;
   rule_218;
   rule_219;
   rule_220;
   rule_221;
   rule_222;
   rule_223;
   rule_224;
   rule_225;
   rule_226;
   rule_227;
   rule_228;
   rule_229;
   rule_230;
   rule_231;
   rule_232;
   rule_233;
   rule_234;
   rule_235;
   rule_236;
   rule_237;
   rule_238;
   rule_239;
   rule_240;
   rule_241;
   rule_242;
   rule_243;
   rule_244;
   rule_245].

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