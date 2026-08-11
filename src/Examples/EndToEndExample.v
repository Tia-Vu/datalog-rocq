(* END-TO-END example: from a source datalog program + an indexed layout, run the real compiler,
   discharge the (decidable) side checks BY COMPUTATION, and obtain a PROOF OF EQUIVALENCE between
   the compiled distributed hardware network and the original program.

   The headline theorem [DistributedDatalogToHardwareCompilerCorrect.nattify_and_compile_correct] is
   stated generically (over arbitrary map instances).  Here we:
     1. pin every instance to the string-datalog / grid-topology backend ([grid_equiv]);
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
From coqutil Require Import Map.Interface Map.SortedListString Result.
From Datalog Require Import Datalog NattifyRel RelMap Map Default.
From DatalogRocq Require Import
  DistributedDatalogToHardwareCompilerCorrect
  DistributedDatalogToHardwareCompiler
  StringDatalogParams StringDatalog StringGridCompiler
  GridTopology GridGraph SortedListNat
  DistributedHardwareProgram DistributedHardwareSemantics.
Import ListNotations.
Open Scope string_scope.

(* Trivial value-signature for the bare fragment (no functions / no aggregation). *)
#[local] Instance sig_src : signature string unit string :=
  {| interp_fun := fun _ _ => None;
     get_nat := fun _ => 0; agg_bop := fun _ x _ => x; agg_id := fun _ => "" |}.

Notation node_id     := GridGraph.Node.

(*==========================================================================*)
(*  The concrete program and indexed layout.                                  *)
(*==========================================================================*)

(* J(x, y) :- A(x, y), B(y, x). *)
Definition ruleJ : rule :=
  Datalog.normal_rule
    [ {| Datalog.clause_rel := "J"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ]
    [ {| Datalog.clause_rel := "A"; Datalog.clause_args := [Datalog.var_expr "x"; Datalog.var_expr "y"] |} ;
      {| Datalog.clause_rel := "B"; Datalog.clause_args := [Datalog.var_expr "y"; Datalog.var_expr "x"] |} ].

Definition P : list rule := [ruleJ].
Definition idx_layout : list (node_id * list nat) := [ ([0; 0]%nat, [0]%nat) ].  (* rule 0 -> node (0,0) *)
Definition topo : GridGraph.Dimensions := [1; 1]%nat.                            (* a 1x1 grid *)

(* [FPS] placeholder I/O locations; [G] the grid graph.  [compile_program] nattifies internally;
   [NLAYOUT]/[NFPS] name the numbered layout/fact-locations it feeds to [compile]. *)
Definition FPS     := all_io_locations P idx_layout topo.
Definition G       := GridTopology.make_topo_graph topo.
Definition NLAYOUT := nattify_layout (rel_ids P) (make_layout_map P idx_layout).
Definition NFPS    := nattify_fact_locs (rel_ids P) FPS.
Definition FT      := dumb_ftables G.(ComputableGraph.edges) NLAYOUT NFPS.

(* The compiler runs and SUCCEEDS (cheap head-constructor check). *)
Definition compiled_J := Eval vm_compute in compile_program P idx_layout FPS FPS topo.
Example compiled_J_ok : match compiled_J with Success _ => True | _ => False end := I.

(* Boolean side checks (reduce to [true = true]). *)
Example check_bare        : bare_layoutb NLAYOUT = true.
Proof. vm_compute; reflexivity. Qed.
Example check_distributes : layout_distributes_programb (nattify_rel_prog (program_rels P) P) NLAYOUT = true.
Proof. vm_compute; reflexivity. Qed.

(*==========================================================================*)
(*  THE END-TO-END EQUIVALENCE, via [grid_equiv] ([nattify_and_compile_correct]  *)
(*  pinned to this backend): the distributed run of the compiled network parks   *)
(*  the nattified [fsrc] at an output node  iff  the SOURCE program [P] derives   *)
(*  [fsrc].  Compiler success is a hypothesis (witnessed cheaply by [compiled_J_ok]). *)
(*==========================================================================*)
Opaque compile.
Theorem end_to_end_equiv
    (ninfos : list (@DistributedHardwareProgram.node_info node_id _))
    (Qsrc : @Datalog.fact string string -> Prop) (fsrc : @Datalog.fact string string) :
  compile_program P idx_layout FPS FPS topo = Success ninfos ->
  (forall f, Qsrc f -> In (Datalog.rel_of f) (program_rels P)) ->
  edb_routable NFPS (relabel_Q (encode_rel (program_rels P) P) Qsrc) ->
  (exists n, In n (get_or_default NFPS (Datalog.rel_of (nattify_rel_fact (program_rels P) P fsrc)))) ->
  run_ninfos ninfos
    (fun n f0 => relabel_Q (encode_rel (program_rels P) P) Qsrc f0 /\
                 In n (get_or_default NFPS (Datalog.rel_of f0)))
    (fun n R  => In n (get_or_default NFPS R))
    (nattify_rel_fact (program_rels P) P fsrc)
  <-> Datalog.prog_impl P Qsrc fsrc.
Proof.
  intros Hc Hscope Hedb Houtrel.
  eapply nattify_and_compile_correct; try eassumption.
  - reflexivity.
  - apply layout_distributes_programb_spec. reflexivity.
Qed.

(*==========================================================================*)
(*  A SECOND, two-rule example: transitive closure, distributed over 2 nodes. *)
(*     Path(x, y) :- Edge(x, y).                                               *)
(*     Path(x, z) :- Edge(x, y), Path(y, z).                                   *)
(*  [grid_equiv] is program/layout-agnostic, so it is reused verbatim.         *)
(*==========================================================================*)
Definition Path (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause_rel := "Path"; Datalog.clause_args := [Datalog.var_expr x; Datalog.var_expr y] |}.
Definition Edge (x y : string) : @Datalog.clause string string string :=
  {| Datalog.clause_rel := "Edge"; Datalog.clause_args := [Datalog.var_expr x; Datalog.var_expr y] |}.

Definition r0 : rule := Datalog.normal_rule [Path "x" "y"] [Edge "x" "y"].
Definition r1 : rule := Datalog.normal_rule [Path "x" "z"] [Edge "x" "y"; Path "y" "z"].
Definition Preach : list rule := [r0; r1].
Definition idx_layout_r : list (node_id * list nat) :=
  [ ([0; 0]%nat, [0]%nat); ([1; 0]%nat, [1]%nat) ].
Definition topo_r : GridGraph.Dimensions := [2; 1]%nat.

Definition FPS_r     := all_io_locations Preach idx_layout_r topo_r.
Definition G_r       := GridTopology.make_topo_graph topo_r.
Definition NLAYOUT_r := nattify_layout (rel_ids Preach) (make_layout_map Preach idx_layout_r).
Definition NFPS_r    := nattify_fact_locs (rel_ids Preach) FPS_r.
Definition FT_r      := dumb_ftables G_r.(ComputableGraph.edges) NLAYOUT_r NFPS_r.

Definition compiled_R := Eval vm_compute in compile_program Preach idx_layout_r FPS_r FPS_r topo_r.
Example compiled_R_ok : match compiled_R with Success _ => True | _ => False end := I.

Example check_bare_r        : bare_layoutb NLAYOUT_r = true.
Proof. vm_compute; reflexivity. Qed.
Example check_distributes_r : layout_distributes_programb (nattify_rel_prog (program_rels Preach) Preach) NLAYOUT_r = true.
Proof. vm_compute; reflexivity. Qed.

Theorem end_to_end_equiv_reach
    (ninfos : list (@DistributedHardwareProgram.node_info node_id _))
    (Qsrc : @Datalog.fact string string -> Prop) (fsrc : @Datalog.fact string string) :
  compile_program Preach idx_layout_r FPS_r FPS_r topo_r = Success ninfos ->
  (forall f, Qsrc f -> In (Datalog.rel_of f) (program_rels Preach)) ->
  edb_routable NFPS_r (relabel_Q (encode_rel (program_rels Preach) Preach) Qsrc) ->
  (exists n, In n (get_or_default NFPS_r (Datalog.rel_of (nattify_rel_fact (program_rels Preach) Preach fsrc)))) ->
  run_ninfos ninfos
    (fun n f0 => relabel_Q (encode_rel (program_rels Preach) Preach) Qsrc f0 /\
                 In n (get_or_default NFPS_r (Datalog.rel_of f0)))
    (fun n R  => In n (get_or_default NFPS_r R))
    (nattify_rel_fact (program_rels Preach) Preach fsrc)
  <-> Datalog.prog_impl Preach Qsrc fsrc.
Proof.
  intros Hc Hscope Hedb Houtrel.
  eapply nattify_and_compile_correct; try eassumption.
  - reflexivity.
  - apply layout_distributes_programb_spec. reflexivity.
Qed.
