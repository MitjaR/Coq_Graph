Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.

(** 
Let us define some graphs. 
**)

(* Empty graph on [n] vertices *)
Definition Empty (n : nat) : Graph.
Proof.
  refine {| V := n ;
            E := (fun x y => False)
         |} ; auto.
Defined.

(* Complete graph on [n] vertices *)
Definition K (n : nat) : Graph.
Proof.
  refine {| V := n ;
            E := (fun x y => x <> y)
         |}.
  - intros.
    destruct (Nat.eq_dec x y) ; tauto.
  - intros x H L.
    absurd (x = x) ; tauto.
  - intros ; now apply not_eq_sym.
Defined.

(* Path on [n] vertices. *)
Definition Path (n : nat) : Graph.
Proof.
  (* We will do this proof very slowly by hand to practice. *)
  refine {| V := n ;
            E := fun x y => S x = y \/ x = S y
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y).
    + tauto.
    + destruct (eq_nat_dec x (S y)).
      * tauto.
      * { right.
          intros [ ? | ? ].
          - absurd (S x = y) ; assumption.
          - absurd (x = S y) ; assumption.
        }
  - (* This case we do by using a powerful tactic "firstorder".
       We tell it to use the statement [n_Sn] from the [Arith] library.
       To see what [n_Sn] is, run command [Check n_Sn].
       To find [n_Sn], we ran the command [Search (?m <> S ?m)]. *)
    firstorder using n_Sn.
  - intros ? ? ? ? [?|?].
    + right ; now symmetry.
    + left; now symmetry.
Defined.


(* [Cycle n] is the cycle on [n+3] vertices. We define it in a way
    which avoids modular arithmetic. *)
Definition Cycle (n : nat) : Graph.
Proof.
  refine {| V := 3 + n ; (* Do not forget: we have [3+n] vertices 0, 1, ..., n+2 *)
            E := fun x y =>
                 ((S x = y \/ x = S y) \/ (x = 0 /\ y = 2 + n) \/ (x = 2 + n /\ y = 0))
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y); auto.
    destruct (eq_nat_dec x (S y)); auto.
    destruct (eq_nat_dec x 0); destruct (eq_nat_dec y (2 + n)); auto;
    destruct (eq_nat_dec y 0); destruct (eq_nat_dec x (2 + n)); tauto.
  - intros ? ? H.
    destruct H as [[?|?]|[[? ?]|[? ?]]].
    + firstorder using Nat.neq_succ_diag_l.
    + firstorder using Nat.neq_succ_diag_r.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
  - intros ? ? ? ? [[?|?]|[[? ?]|[? ?]]].
    + left; right; now symmetry.
    + left; left; now symmetry.
    + auto.
    + auto.
Defined.


