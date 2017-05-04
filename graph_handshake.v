Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import numeric_even.
Require Import kernel_graph_extensions.

Theorem hand_shake_rv (G : Graph) :
  sum' (V G) (degree G) = 2 * edges G.
Proof.
  rewrite hand_shake; auto.
Qed.

Theorem hand_shake_theorem_part (G : Graph) :
  (Nat.Even (sum' (V G) (degree G))) -> 
  (Nat.Even (count (V G) (fun x => odd_dec (degree G x)))).
Proof.
  apply even_odds_in_even.
Qed.


Theorem hand_shake_theorem (G : Graph) :
  Nat.Even (count (V G) (fun x => odd_dec (degree G x))).
Proof.
  apply hand_shake_theorem_part.
  rewrite hand_shake_rv.
  unfold Nat.Even.
  exists (edges G).
  auto.
Qed.

