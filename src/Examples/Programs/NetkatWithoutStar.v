From Stdlib Require Import Strings.String List.
From Datalog Require Import Datalog.
From DatalogRocq Require Import StringDatalogParams DependencyGenerator.
Import ListNotations.
Open Scope string_scope.

Import StringDatalogParams.
#[local] Instance string_fn : fnT := string.

(* Operator meanings *)
(* ================================================================= *)
(* Disj = \/          Boolean OR *)
(* Conj = /\          Boolean AND *)
(* Not = ~            Boolean NOT *)
(* Parallel = +       Parallel composition *)
(* Seq = ;            Sequential composition *)
(* Star = *           Kleene star / repetition *)
(* Assn = :=          Assignment *)
(* Match = ==         Boolean Check *)
(* Drop = 0           Annihilation / zero element *)
(* Id = 1             Identity element *)

(* Plain (non-fancy) helpers replacing the old FancyNotations: NetKAT term constructors
   are just function symbols ([expr.app]) and the two relations ([Term], [rewrite]) are
   plain [clause]s.  [v "x"] is a variable. *)
Local Definition v (s : string) : expr := expr.var s.
Local Definition Disj (a b : expr) : expr := expr.app "Disj" [a; b].
Local Definition Conj (a b : expr) : expr := expr.app "Conj" [a; b].
Local Definition Parallel (a b : expr) : expr := expr.app "Parallel" [a; b].
Local Definition Seq (a b : expr) : expr := expr.app "Seq" [a; b].
Local Definition Assn (a b : expr) : expr := expr.app "Assn" [a; b].
Local Definition Match (a b : expr) : expr := expr.app "Match" [a; b].
Local Definition Filter (a : expr) : expr := expr.app "Filter" [a].
Local Definition Not (a : expr) : expr := expr.app "Not" [a].
Local Definition Drop : expr := expr.app "Drop" [].
Local Definition Id : expr := expr.app "Id" [].
Local Definition Term (e : expr) : clause := {| clause.rel := "Term"; clause.args := [e] |}.
Local Definition rw (a b : expr) : clause := {| clause.rel := "rewrite"; clause.args := [a; b] |}.

(* ================= Associativity ================= *)

(* a \/ (b \/ c) -> (a \/ b) \/ c *)
Definition r_disj_assoc_l : rule :=
  rule.impl
    [ Term (Disj (Disj (v "a") (v "b")) (v "c"));
      rw (Disj (v "a") (Disj (v "b") (v "c"))) (Disj (Disj (v "a") (v "b")) (v "c")) ]
    [ Term (Disj (v "a") (Disj (v "b") (v "c"))) ].

(* (a \/ b) \/ c -> a \/ (b \/ c) *)
Definition r_disj_assoc_r : rule :=
  rule.impl
    [ Term (Disj (v "a") (Disj (v "b") (v "c")));
      rw (Disj (Disj (v "a") (v "b")) (v "c")) (Disj (v "a") (Disj (v "b") (v "c"))) ]
    [ Term (Disj (Disj (v "a") (v "b")) (v "c")) ].

(* a /\ (b /\ c) -> (a /\ b) /\ c *)
Definition r_conj_assoc_l : rule :=
  rule.impl
    [ Term (Conj (Conj (v "a") (v "b")) (v "c"));
      rw (Conj (v "a") (Conj (v "b") (v "c"))) (Conj (Conj (v "a") (v "b")) (v "c")) ]
    [ Term (Conj (v "a") (Conj (v "b") (v "c"))) ].

(* (a /\ b) /\ c -> a /\ (b /\ c) *)
Definition r_conj_assoc_r : rule :=
  rule.impl
    [ Term (Conj (v "a") (Conj (v "b") (v "c")));
      rw (Conj (Conj (v "a") (v "b")) (v "c")) (Conj (v "a") (Conj (v "b") (v "c"))) ]
    [ Term (Conj (Conj (v "a") (v "b")) (v "c")) ].

(* p + (q + r) -> (p + q) + r *)
Definition r_parallel_assoc_l : rule :=
  rule.impl
    [ Term (Parallel (Parallel (v "p") (v "q")) (v "r"));
      rw (Parallel (v "p") (Parallel (v "q") (v "r"))) (Parallel (Parallel (v "p") (v "q")) (v "r")) ]
    [ Term (Parallel (v "p") (Parallel (v "q") (v "r"))) ].

(* (p + q) + r -> p + (q + r) *)
Definition r_parallel_assoc_r : rule :=
  rule.impl
    [ Term (Parallel (v "p") (Parallel (v "q") (v "r")));
      rw (Parallel (Parallel (v "p") (v "q")) (v "r")) (Parallel (v "p") (Parallel (v "q") (v "r"))) ]
    [ Term (Parallel (Parallel (v "p") (v "q")) (v "r")) ].

(* (p ; q) ; r -> p ; (q ; r) *)
Definition r_seq_assoc_l : rule :=
  rule.impl
    [ Term (Seq (Seq (v "p") (v "q")) (v "r"));
      rw (Seq (v "p") (Seq (v "q") (v "r"))) (Seq (Seq (v "p") (v "q")) (v "r")) ]
    [ Term (Seq (v "p") (Seq (v "q") (v "r"))) ].

(* p ; (q ; r) -> (p ; q) ; r *)
Definition r_seq_assoc_r : rule :=
  rule.impl
    [ Term (Seq (v "p") (Seq (v "q") (v "r")));
      rw (Seq (Seq (v "p") (v "q")) (v "r")) (Seq (v "p") (Seq (v "q") (v "r"))) ]
    [ Term (Seq (Seq (v "p") (v "q")) (v "r")) ].

(* ================= Commutativity ================= *)

(* a \/ b -> b \/ a *)
Definition r_disj_comm : rule :=
  rule.impl
    [ Term (Disj (v "b") (v "a"));
      rw (Disj (v "a") (v "b")) (Disj (v "b") (v "a")) ]
    [ Term (Disj (v "a") (v "b")) ].

(* a /\ b -> b /\ a *)
Definition r_conj_comm : rule :=
  rule.impl
    [ Term (Conj (v "b") (v "a"));
      rw (Conj (v "a") (v "b")) (Conj (v "b") (v "a")) ]
    [ Term (Conj (v "a") (v "b")) ].

(* p + q -> q + p *)
Definition r_parallel_comm : rule :=
  rule.impl
    [ Term (Parallel (v "q") (v "p"));
      rw (Parallel (v "p") (v "q")) (Parallel (v "q") (v "p")) ]
    [ Term (Parallel (v "p") (v "q")) ].

(* ================= Identities ================= *)

(* a \/ 0 -> a *)
Definition r_disj_id : rule :=
  rule.impl
    [ Term (v "a");
      rw (Disj (v "a") Drop) (v "a") ]
    [ Term (Disj (v "a") Drop) ].

(* p + 0 -> p *)
Definition r_parallel_filter_drop : rule :=
  rule.impl
    [ Term (v "p");
      rw (Parallel (v "p") (Filter Drop)) (v "p") ]
    [ Term (Parallel (v "p") (Filter Drop)) ].

(* a /\ 1 -> a *)
Definition r_conj_id : rule :=
  rule.impl
    [ Term (v "a");
      rw (Conj (v "a") Id) (v "a") ]
    [ Term (Conj (v "a") Id) ].

(* 1 ; p -> p *)
Definition r_seq_filter_id_l : rule :=
  rule.impl
    [ Term (v "p");
      rw (Seq (Filter Id) (v "p")) (v "p") ]
    [ Term (Seq (Filter Id) (v "p")) ].

(* p ; 1 -> p *)
Definition r_seq_filter_id_r : rule :=
  rule.impl
    [ Term (v "p");
      rw (Seq (v "p") (Filter Id)) (v "p") ]
    [ Term (Seq (v "p") (Filter Id)) ].

(* ================= Annihilation ================= *)

(* a /\ 0 -> 0 *)
Definition r_conj_drop : rule :=
  rule.impl
    [ Term Drop;
      rw (Conj (v "a") Drop) Drop ]
    [ Term (Conj (v "a") Drop) ].

(* p ; 0 -> 0 *)
Definition r_seq_filter_drop_l : rule :=
  rule.impl
    [ Term (Filter Drop);
      rw (Seq (Filter Drop) (v "p")) (Filter Drop) ]
    [ Term (Seq (Filter Drop) (v "p")) ].

(* 0 ; p -> 0 *)
Definition r_seq_filter_drop_r : rule :=
  rule.impl
    [ Term (Filter Drop);
      rw (Seq (v "p") (Filter Drop)) (Filter Drop) ]
    [ Term (Seq (v "p") (Filter Drop)) ].

(* ================= Idempotence ================= *)

(* a \/ a -> a *)
Definition r_disj_idempotent : rule :=
  rule.impl
    [ Term (v "a");
      rw (Disj (v "a") (v "a")) (v "a") ]
    [ Term (Disj (v "a") (v "a")) ].

(* p + p -> p *)
Definition r_parallel_idempotent : rule :=
  rule.impl
    [ Term (v "p");
      rw (Parallel (v "p") (v "p")) (v "p") ]
    [ Term (Parallel (v "p") (v "p")) ].

(* ================= Distributivity ================= *)

(* a /\ (b \/ c) -> (a /\ b) \/ (a /\ c) *)
Definition r_conj_disj_dist_l : rule :=
  rule.impl
    [ Term (Disj (Conj (v "a") (v "b")) (Conj (v "a") (v "c")));
      rw (Conj (v "a") (Disj (v "b") (v "c"))) (Disj (Conj (v "a") (v "b")) (Conj (v "a") (v "c"))) ]
    [ Term (Conj (v "a") (Disj (v "b") (v "c"))) ].

(* (a /\ b) \/ (a /\ c) -> a /\ (b \/ c) *)
Definition r_conj_disj_dist_r : rule :=
  rule.impl
    [ Term (Conj (v "a") (Disj (v "b") (v "c")));
      rw (Disj (Conj (v "a") (v "b")) (Conj (v "a") (v "c"))) (Conj (v "a") (Disj (v "b") (v "c"))) ]
    [ Term (Disj (Conj (v "a") (v "b")) (Conj (v "a") (v "c"))) ].

(* ================= Boolean Algebra Axioms ================= *)

(* a \/ 1 -> 1 *)
Definition r_disj_id_plus : rule :=
  rule.impl
    [ Term Id;
      rw (Disj (v "a") Id) Id ]
    [ Term (Disj (v "a") Id) ].

(* a \/ ~a -> 1 *)
Definition r_disj_not : rule :=
  rule.impl
    [ Term Id;
      rw (Disj (v "a") (Not (v "a"))) Id ]
    [ Term (Disj (v "a") (Not (v "a"))) ].

(* a /\ ~a -> 0 *)
Definition r_conj_not : rule :=
  rule.impl
    [ Term Drop;
      rw (Conj (v "a") (Not (v "a"))) Drop ]
    [ Term (Conj (v "a") (Not (v "a"))) ].

(* ================= Packet / Sequential Axioms ================= *)

(* f1 := n1 ; f2 := n2 -> f2 := n2 ; f1 := n1 when f1 != f2 *)
(* TODO encode the NEQ for f1 and f2 *)
Definition r_mod_comm : rule :=
  rule.impl
    [ Term (Seq (Assn (v "f2") (v "n2")) (Assn (v "f1") (v "n1")));
      rw (Seq (Assn (v "f1") (v "n1")) (Assn (v "f2") (v "n2")))
         (Seq (Assn (v "f2") (v "n2")) (Assn (v "f1") (v "n1"))) ]
    [ Term (Seq (Assn (v "f1") (v "n1")) (Assn (v "f2") (v "n2"))) ].

(* f1 := n1 ; f2 == n2 -> f2 == n2 ; f1 := n1 when f2 != f1 *)
Definition r_mod_filter_comm1 : rule :=
  rule.impl
    [ Term (Seq (Assn (v "f1") (v "n1")) (Filter (Match (v "f2") (v "n2"))));
      rw (Seq (Filter (Match (v "f2") (v "n2"))) (Assn (v "f1") (v "n1")))
         (Seq (Assn (v "f1") (v "n1")) (Filter (Match (v "f2") (v "n2")))) ]
    [ Term (Seq (Assn (v "f1") (v "n1")) (Filter (Match (v "f2") (v "n2")))) ].

(* f1 == n1 ; f2 := n2 -> f2 := n2 ; f1 == n1 when f2 != f1 *)
Definition r_mod_filter_comm2 : rule :=
  rule.impl
    [ Term (Seq (Filter (Match (v "f1") (v "n1"))) (Assn (v "f2") (v "n2")));
      rw (Seq (Assn (v "f2") (v "n2")) (Filter (Match (v "f1") (v "n1"))))
         (Seq (Filter (Match (v "f1") (v "n1"))) (Assn (v "f2") (v "n2"))) ]
    [ Term (Seq (Filter (Match (v "f1") (v "n1"))) (Assn (v "f2") (v "n2"))) ].

(* f := n ; f == n -> f := n *)
Definition r_mod_filter : rule :=
  rule.impl
    [ Term (Assn (v "f") (v "n"));
      rw (Seq (Assn (v "f") (v "n")) (Filter (Match (v "f") (v "n")))) (Assn (v "f") (v "n")) ]
    [ Term (Seq (Assn (v "f") (v "n")) (Filter (Match (v "f") (v "n")))) ].

(* f == n ; f := n -> f == n *)
Definition r_filter_mod : rule :=
  rule.impl
    [ Term (Filter (Match (v "f") (v "n")));
      rw (Seq (Filter (Match (v "f") (v "n"))) (Assn (v "f") (v "n"))) (Filter (Match (v "f") (v "n"))) ]
    [ Term (Seq (Filter (Match (v "f") (v "n"))) (Assn (v "f") (v "n"))) ].

(* f == n1 ; f == n2 -> 0 when n1 != n2 *)
(* TODO encode the NEQ for n1 and n2 *)
Definition r_filter_contradiction : rule :=
  rule.impl
    [ Term (Filter Drop);
      rw (Seq (Filter (Match (v "f") (v "n1"))) (Filter (Match (v "f") (v "n2")))) (Filter Drop) ]
    [ Term (Seq (Filter (Match (v "f") (v "n1"))) (Filter (Match (v "f") (v "n2")))) ].

(* f := n ; f := n -> f := n *)
Definition r_twice_mod : rule :=
  rule.impl
    [ Term (Assn (v "f") (v "n"));
      rw (Seq (Assn (v "f") (v "n")) (Assn (v "f") (v "n"))) (Assn (v "f") (v "n")) ]
    [ Term (Seq (Assn (v "f") (v "n")) (Assn (v "f") (v "n"))) ].

(* ================= Equality Between Algebras ================= *)

(* a \/ b -> Filter a + Filter b *)
Definition r_filter_disj : rule :=
  rule.impl
    [ Term (Parallel (Filter (v "a")) (Filter (v "b")));
      rw (Filter (Disj (v "a") (v "b"))) (Parallel (Filter (v "a")) (Filter (v "b"))) ]
    [ Term (Filter (Disj (v "a") (v "b"))) ].

(* Filter a + Filter b -> Filter (a \/ b) *)
Definition r_parallel_filter : rule :=
  rule.impl
    [ Term (Filter (Disj (v "a") (v "b")));
      rw (Parallel (Filter (v "a")) (Filter (v "b"))) (Filter (Disj (v "a") (v "b"))) ]
    [ Term (Parallel (Filter (v "a")) (Filter (v "b"))) ].

(* Filter(a) ; Filter(b) -> Filter(a /\ b) *)
Definition r_filter_conj : rule :=
  rule.impl
    [ Term (Filter (Conj (v "a") (v "b")));
      rw (Seq (Filter (v "a")) (Filter (v "b"))) (Filter (Conj (v "a") (v "b"))) ]
    [ Term (Seq (Filter (v "a")) (Filter (v "b"))) ].

(* Filter(a /\ b) -> Filter(a) ; Filter(b) *)
Definition r_seq_filter : rule :=
  rule.impl
    [ Term (Seq (Filter (v "a")) (Filter (v "b")));
      rw (Filter (Conj (v "a") (v "b"))) (Seq (Filter (v "a")) (Filter (v "b"))) ]
    [ Term (Seq (Filter (v "a")) (Filter (v "b"))) ].

Definition r_backwards_congruence : rule :=
  rule.impl
    [ rw (v "a") (v "b") ]
    [ rw (Filter (v "a")) (Filter (v "b")) ].

Definition r_rewrite_transitive : rule :=
  rule.impl
    [ rw (v "a") (v "c") ]
    [ rw (v "a") (v "b");
      rw (v "b") (v "c") ].

(* ================= Term Closure Rules ================= *)

(* If Disj(a, b) is a term, then a and b are terms *)
Definition r_disj_subterms : rule :=
  rule.impl
    [ Term (v "a"); Term (v "b") ]
    [ Term (Disj (v "a") (v "b")) ].

(* If Conj(a, b) is a term, then a and b are terms *)
Definition r_conj_subterms : rule :=
  rule.impl
    [ Term (v "a"); Term (v "b") ]
    [ Term (Conj (v "a") (v "b")) ].

(* If Seq(p, q) is a term, then p and q are terms *)
Definition r_seq_subterms : rule :=
  rule.impl
    [ Term (v "p"); Term (v "q") ]
    [ Term (Seq (v "p") (v "q")) ].

(* If Parallel(p, q) is a term, then p and q are terms *)
Definition r_parallel_subterms : rule :=
  rule.impl
    [ Term (v "p"); Term (v "q") ]
    [ Term (Parallel (v "p") (v "q")) ].

(* If Filter(a) is a term, then a is a term *)
Definition r_filter_subterm : rule :=
  rule.impl
    [ Term (v "a") ]
    [ Term (Filter (v "a")) ].

(* If Not(a) is a term, then a is a term *)
Definition r_not_subterm : rule :=
  rule.impl
    [ Term (v "a") ]
    [ Term (Not (v "a")) ].


(* ================= Program ================= *)

Definition netkat_program : list rule :=
  [
    r_disj_assoc_l; r_disj_assoc_r;
    r_conj_assoc_l; r_conj_assoc_r;
    r_parallel_assoc_l; r_parallel_assoc_r;
    r_seq_assoc_l; r_seq_assoc_r;
    r_disj_comm; r_conj_comm; r_parallel_comm;
    r_disj_id; r_parallel_filter_drop; r_conj_id;
    r_seq_filter_id_l; r_seq_filter_id_r;
    r_conj_drop; r_seq_filter_drop_l; r_seq_filter_drop_r;
    r_disj_idempotent; r_parallel_idempotent;
    r_conj_disj_dist_l; r_conj_disj_dist_r;
    r_disj_id_plus; r_disj_not; r_conj_not;
    r_mod_comm; r_mod_filter_comm1; r_mod_filter_comm2;
    r_mod_filter; r_filter_mod; r_filter_contradiction; r_twice_mod;
    r_filter_disj; r_parallel_filter; r_filter_conj; r_seq_filter;
    r_backwards_congruence;
    r_rewrite_transitive; r_disj_subterms; r_conj_subterms;
    r_seq_subterms; r_parallel_subterms; r_filter_subterm; r_not_subterm
  ].


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

(* Example computations *)
Compute get_program_dependencies netkat_program.
Compute get_rule_dependencies
        netkat_program
        r_disj_subterms.

Compute get_program_dependencies_flat netkat_program.
