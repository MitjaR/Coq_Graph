Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import numeric_even.
Require Import kernel_graph_extensions.

(* 
Hand shaking lemma (Lema o rokovanju):
We work towards a general theorem: 
the number of vertices with odd degree is even. 
*)

Lemma sum_sum_ULD_rv (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => sum' n (fun y => f x y)) = 
  sum' n (fun x => (sum' x (fun y => f x y))) + 
  sum' n (fun x => (sum' x (fun y => f y x))) + 
  sum' n (fun x => (f x x)).
Proof.
  rewrite sum_sum_ULD.
  auto.
Qed.

Theorem E_irreflexive_graph (G : Graph):
  all x : (V G), ((if E_decidable G x x then 1 else 0) = 0).
Proof.
  intros x p.
  destruct (E_decidable G x x).
  - pose (E_irreflexive G x p).
    absurd (G x x); auto.
  - auto.
Qed.
  

Theorem handshake_part0 (G : Graph):
  sum' G (fun x : nat => if E_decidable G x x then 1 else 0) = 
  sum' G (fun x : nat => 0).
Proof.
  apply change_sum'.
  apply E_irreflexive_graph.
Qed.

Theorem handshake_part1 (G : Graph):
  sum' G (fun x : nat => if E_decidable G x x then 1 else 0) = 0.
Proof.
  rewrite handshake_part0.
  rewrite (sum_n_krat_k (V G) 0).
  auto.
Qed.
  

Theorem handshake_part2 (G : Graph):
  sum' (V G) (fun x : nat => sum' (V G) (fun y : nat => if E_decidable G x y then 1 else 0)) = 
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G x y then 1 else 0))) +
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G y x then 1 else 0))).
Proof.
  (* uporabim lasnost vsote in pokazem da G x x vedno enako 0*)
  rewrite sum_sum_ULD_rv.
  rewrite handshake_part1.
  omega.
Qed.

Theorem handshake_part3 (G : Graph):
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G x y then 1 else 0))) =
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G y x then 1 else 0))).
Proof.
  apply change_sum'.
  intros x p.
  apply change_sum'.
  intros y q.
  apply (edges_symmetry G x p y (Nat.lt_trans y x (V G) q p)).
Qed.

Theorem handshake (G : Graph) :
  2 * edges G = sum' (V G) (degree G).
Proof.
  unfold edges.
  unfold degree.
  unfold count.
  rewrite handshake_part2.
  rewrite handshake_part3.
  omega.
Qed.






Theorem handshake_rv (G : Graph) :
  sum' (V G) (degree G) = 2 * edges G.
Proof.
  rewrite handshake; auto.
Qed.

Theorem handshake_theorem_part (G : Graph) :
  (Nat.Even (sum' (V G) (degree G))) -> 
  (Nat.Even (count (V G) (fun x => odd_dec (degree G x)))).
Proof.
  apply even_odds_in_even.
Qed.


Theorem handshake_theorem (G : Graph) :
  Nat.Even (count (V G) (fun x => odd_dec (degree G x))).
Proof.
  apply handshake_theorem_part.
  rewrite handshake_rv.
  unfold Nat.Even.
  exists (edges G).
  auto.
Qed.



