(* END-TO-END example: from a source datalog program + an indexed layout, run the real compiler,
   discharge the (decidable) side checks BY COMPUTATION, and obtain a PROOF OF EQUIVALENCE between
   the compiled distributed hardware network and the original program.

   The headline theorem [DistributedDatalogToHardwareCompilerCorrect.nattify_and_compile_correct] is
   stated generically (over arbitrary map instances).  Here we:
     1. instantiate it at the string-datalog / grid-topology backend (its maps are inferred);
     2. give a concrete program  J(x,y) :- A(x,y), B(y,x)  and a one-node indexed layout;
     3. run the compiler ([compiled_J]) and show it SUCCEEDS;
     4. discharge the boolean side checks [bare_layoutb] / [layout_distributes_programb] by [vm_compute];
     5. conclude [end_to_end_equiv]: for the compiler's output [ninfos], the distributed run derives
        the nattified [fsrc] iff the source program derives [fsrc].

   Note on performance: proving  compile ... = Success ninfos  as a full Leibniz equality is slow,
   because the kernel re-checks the [eq_refl] sortedness proofs inside every emitted sorted-list map
   WITHOUT the VM.  So the equivalence takes the compiler's output as a hypothesis; that the equation
   holds is witnessed cheaply by [compiled_J_ok] (a [match ... => True], which never forces the map
   proofs).  The boolean checks, by contrast, reduce to [true = true] and are cheap.

   A successful build IS the test. *)

From Stdlib Require Import List String.
From coqutil Require Import Map.Interface Result.
From Datalog Require Import Datalog NattifyRel RelMap.
From Datalog.Util Require Import Map Default.
From DatalogRocq Require Import
  DistributedDatalogToHardwareCompilerCorrect
  DistributedDatalogToHardwareCompiler
  StringDatalogParams StringDatalog StringGridCompiler
  GridTopology GridGraph MapInstances
  DistributedHardwareProgram DistributedHardwareSemantics.
Import ListNotations.
Open Scope string_scope.

(* Trivial value-signature for the bare fragment (no functions / no aggregation). *)
#[local] Instance sig_src : datalog_semantics string unit string :=
  {| interp_fun := fun _ _ => None;
     get_nat := fun _ => 0; agg_bop := fun _ x _ => x; agg_id := fun _ => "" |}.

Local Abbreviation rules_only p := {| program.rules := p; program.meta_rules := [] |}.

Abbreviation node_id := GridGraph.Node.

(*==========================================================================*)
(*  The concrete program and indexed layout.                                  *)
(*==========================================================================*)

(* J(x, y) :- A(x, y), B(y, x). *)
Definition ruleJ : rule :=
  Datalog.rule.impl
    [ {| Datalog.clause.rel := "J"; Datalog.clause.args := [Datalog.expr.var "x"; Datalog.expr.var "y"] |} ]
    [ {| Datalog.clause.rel := "A"; Datalog.clause.args := [Datalog.expr.var "x"; Datalog.expr.var "y"] |} ;
      {| Datalog.clause.rel := "B"; Datalog.clause.args := [Datalog.expr.var "y"; Datalog.expr.var "x"] |} ].

Definition P : list rule := [ruleJ].
Definition idx_layout : list (node_id * list nat) := [ ([0; 0]%nat, [0]%nat) ].  (* rule 0 -> node (0,0) *)
Definition topo : GridGraph.Dimensions := [1; 1]%nat.                            (* a 1x1 grid *)

(* [FPS] placeholder I/O locations; [G] the grid graph.  [compile_program] nattifies internally;
   [NLAYOUT]/[NFPS] name the numbered layout/fact-locations it feeds to [compile]. *)
Definition FPS     := all_io_locations P idx_layout topo.
Definition G       := GridTopology.make_topo_graph topo.
Definition NLAYOUT := nattify_layout (rel_ids P) (make_layout_map P idx_layout).
Definition NFPS    := nattify_fact_locs (rel_ids P) FPS.

(* The compiler runs and SUCCEEDS (cheap head-constructor check). *)
Definition compiled_J := Eval vm_compute in compile_program P idx_layout FPS FPS topo.
Example compiled_J_ok : match compiled_J with Success _ => True | _ => False end := I.

(* Boolean side checks (reduce to [true = true]). *)
Example check_bare        : bare_layoutb NLAYOUT = true.
Proof. vm_compute; reflexivity. Qed.
Example check_distributes : layout_distributes_programb (nattify_rel_prog (program_rels P) (rules_only P)).(program.rules) NLAYOUT = true.
Proof. vm_compute; reflexivity. Qed.

(*==========================================================================*)
(*  THE END-TO-END EQUIVALENCE, via [nattify_and_compile_correct]: the         *)
(*  distributed run of the compiled network parks                                *)
(*  the nattified [fsrc] at an output node  iff  the SOURCE program [P] derives   *)
(*  [fsrc].  Compiler success is a hypothesis (witnessed cheaply by [compiled_J_ok]). *)
(*==========================================================================*)
Opaque compile.
Theorem end_to_end_equiv
    (ninfos : list (@DistributedHardwareProgram.node_info node_id _))
    (Qsrc : Datalog.fact -> Prop) (fsrc : Datalog.fact) :
  compile_program P idx_layout FPS FPS topo = Success ninfos ->
  (forall f, Qsrc f -> In (fact.rel f) (program_rels P)) ->
  edb_routable NFPS (relabel_Q (encode_rel (rel_table (program_rels P) (rules_only P))) Qsrc) ->
  (exists n, In n (get_or_default NFPS (fact.rel (nattify_rel_fact (program_rels P) (rules_only P) fsrc)))) ->
  run_ninfos ninfos
    (fun n f0 => relabel_Q (encode_rel (rel_table (program_rels P) (rules_only P))) Qsrc f0 /\
                 In n (get_or_default NFPS (fact.rel f0)))
    (nattify_rel_fact (program_rels P) (rules_only P) fsrc)
  <-> program.interp (rules_only P) Qsrc fsrc.
Proof.
  intros Hc Hscope Hedb Houtrel.
  eapply nattify_and_compile_correct; try eassumption.
  - vm_compute; reflexivity.
  - apply layout_distributes_programb_spec. vm_compute; reflexivity.
Qed.

(*==========================================================================*)
(*  A SECOND, two-rule example: transitive closure, distributed over 2 nodes. *)
(*     Path(x, y) :- Edge(x, y).                                               *)
(*     Path(x, z) :- Edge(x, y), Path(y, z).                                   *)
(*  [nattify_and_compile_correct] applies to it unchanged.                    *)
(*==========================================================================*)
Definition Path (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause.rel := "Path"; Datalog.clause.args := [Datalog.expr.var x; Datalog.expr.var y] |}.
Definition Edge (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause.rel := "Edge"; Datalog.clause.args := [Datalog.expr.var x; Datalog.expr.var y] |}.

Definition r0 : rule := Datalog.rule.impl [Path "x" "y"] [Edge "x" "y"].
Definition r1 : rule := Datalog.rule.impl [Path "x" "z"] [Edge "x" "y"; Path "y" "z"].
Definition Preach : list rule := [r0; r1].
Definition idx_layout_r : list (node_id * list nat) :=
  [ ([0; 0]%nat, [0]%nat); ([1; 0]%nat, [1]%nat) ].
Definition topo_r : GridGraph.Dimensions := [2; 1]%nat.

Definition FPS_r     := all_io_locations Preach idx_layout_r topo_r.
Definition G_r       := GridTopology.make_topo_graph topo_r.
Definition NLAYOUT_r := nattify_layout (rel_ids Preach) (make_layout_map Preach idx_layout_r).
Definition NFPS_r    := nattify_fact_locs (rel_ids Preach) FPS_r.

Definition compiled_R := Eval vm_compute in compile_program Preach idx_layout_r FPS_r FPS_r topo_r.
Example compiled_R_ok : match compiled_R with Success _ => True | _ => False end := I.

Example check_bare_r        : bare_layoutb NLAYOUT_r = true.
Proof. vm_compute; reflexivity. Qed.
Example check_distributes_r : layout_distributes_programb (nattify_rel_prog (program_rels Preach) (rules_only Preach)).(program.rules) NLAYOUT_r = true.
Proof. vm_compute; reflexivity. Qed.

Theorem end_to_end_equiv_reach
    (ninfos : list (@DistributedHardwareProgram.node_info node_id _))
    (Qsrc : Datalog.fact -> Prop) (fsrc : Datalog.fact) :
  compile_program Preach idx_layout_r FPS_r FPS_r topo_r = Success ninfos ->
  (forall f, Qsrc f -> In (fact.rel f) (program_rels Preach)) ->
  edb_routable NFPS_r (relabel_Q (encode_rel (rel_table (program_rels Preach) (rules_only Preach))) Qsrc) ->
  (exists n, In n (get_or_default NFPS_r (fact.rel (nattify_rel_fact (program_rels Preach) (rules_only Preach) fsrc)))) ->
  run_ninfos ninfos
    (fun n f0 => relabel_Q (encode_rel (rel_table (program_rels Preach) (rules_only Preach))) Qsrc f0 /\
                 In n (get_or_default NFPS_r (fact.rel f0)))
    (nattify_rel_fact (program_rels Preach) (rules_only Preach) fsrc)
  <-> program.interp (rules_only Preach) Qsrc fsrc.
Proof.
  intros Hc Hscope Hedb Houtrel.
  eapply nattify_and_compile_correct; try eassumption.
  - vm_compute; reflexivity.
  - apply layout_distributes_programb_spec. vm_compute; reflexivity.
Qed.
