Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import graph_constructions.

(** 
Graph constructions properties. 
**)

(*
Search (_ + _ = _ + _  -> _ = _).
*)

(* Dodana tocka trditve. *)
(*#####>*)

Theorem graph_add_point_clear_point_more (G : Graph): 
  V (graph_add_point_clear G) = 1 + (V G).
Proof.
  auto.
Qed.

Theorem graph_add_point_clear_edges_part1 (G : Graph):
  all x : (V G), 
    ((if (E_decidable (graph_add_point_clear G) (V G) x) 
    then 1 else 0) = 0).
Proof.
  intros x p.
  destruct (E_decidable (graph_add_point_clear G) G x).
  - destruct e.
    omega.
  - auto.
Qed.

Theorem graph_add_point_clear_edges_part2 (G : Graph):
  count G (E_decidable (graph_add_point_clear G) G) = 
  sum' G (fun x : nat => 0).
Proof.
  unfold count.
  apply change_sum.
  intros j p.
  pose (graph_add_point_clear_edges_part1 G j p). (* tu bi rad ' (crtico)*)
  apply e.
Qed.
  
Theorem graph_add_point_clear_edges_part3 (G : Graph):
  count G (E_decidable (graph_add_point_clear G) G) = 0.
  rewrite graph_add_point_clear_edges_part2.
  rewrite (sum_n_krat_k (V G) 0).
  auto.
Qed.


Theorem graph_add_point_clear_edges_part4 (G : Graph):
  (all x : V G , all y : V G, 
  ((if E_decidable G x y then 1 else 0) =
  (if E_decidable (graph_add_point_clear G) x y then 1 else 0))).
Proof.
  intros x p y q.
  destruct (E_decidable (graph_add_point_clear G) x y); destruct (E_decidable G x y); auto.
  - destruct e; absurd (G x y); destruct H0; auto.
  - absurd ((graph_add_point_clear G) x y). (* Se to da drugace? *)
    + auto.
    + simpl.
      auto.
Qed.

Theorem graph_add_point_clear_edges (G : Graph): 
  edges (graph_add_point_clear G) = edges G.
Proof.
  unfold edges.
  replace (V (graph_add_point_clear G)) with (S (V G)).
  - rewrite sum'_S.
    replace (sum' G (fun x : nat => count x (E_decidable (graph_add_point_clear G) x))) 
      with (sum' G (fun x : nat => count x (E_decidable G x))).
    + replace (count G (E_decidable (graph_add_point_clear G) G)) with 0.
      * auto.
      * rewrite graph_add_point_clear_edges_part3.
        auto.
    + apply change_sum.
      intros j p.
      apply change_sum.
      intros i q.
      (* tega spodaj ne maram inline *)
      (* tegale: (Nat.lt_trans i j (V G) q p) *)
      (* ali se da drugace? -> ja uporabim assert*)
      apply (graph_add_point_clear_edges_part4 G j p i (Nat.lt_trans i j (V G) q p)).
  - replace (S (V G)) with (1 + (V G)).
    + apply (graph_add_point_clear_point_more G).
    + omega.
Qed.

(*#####<*)
(* Dodana tocka trditve. *)


(* Stozec trditve. *)

Theorem stozec_ima_tocko_vec: 
  (forall G : Graph, V (graph_add_point_full G) = 1 + (V G)).
Proof.
  intro.
  auto.
Qed.

Theorem stozec_edges_part1 (G : Graph):
  all x : (V G), 
    ((if (E_decidable (graph_add_point_full G) (V G) x) 
    then 1 else 0) = 1).
Proof.
  intros x p.
  destruct (E_decidable (graph_add_point_full G) G x).
  - auto.
  - absurd ((graph_add_point_full G) G x).
    + auto.
    + simpl.
      auto. 
Qed.

Theorem stozec_edges_part2 (G : Graph):
  count G (E_decidable (graph_add_point_full G) (V G)) = 
  sum' G (fun x : nat => 1).
Proof.
  unfold count.
  apply change_sum.
  intros j p.
  apply (stozec_edges_part1 G j p).
Qed.
  
Theorem stozec_edges_part3 (G : Graph):
  count G (E_decidable (graph_add_point_full G) G) = (V G).
  rewrite stozec_edges_part2.
  rewrite (sum_n_krat_k (V G) 1).
  omega.
Qed.

Theorem stozec_edges_part4 (G : Graph):
  (all x : V G , all y : V G, 
  ((if E_decidable G x y then 1 else 0) =
  (if E_decidable (graph_add_point_full G) x y then 1 else 0))).
Proof.
  intros x p y q.
  destruct (E_decidable (graph_add_point_full G) x y).
  - destruct e; destruct (E_decidable G x y); auto; absurd (G x y); auto.
    + apply H.
    + omega.
  - destruct (E_decidable G x y); auto.
    absurd((graph_add_point_full G) x y); auto.
    simpl; auto.
Qed.

(*
Search (_ + _ = _ + _ -> _ = _).
*)
(*
Search (_ + _ = _ + _).
*)
(*
Search (_ = _ -> _ + _ = _ + _ ).
*)

Theorem krajsanje (p n m : nat):
  (n = m) -> (p + n = p + m).
Proof.
  omega.
Qed.

Theorem stozec_ima_vec_povezav (G : Graph): 
  edges (graph_add_point_full G) = (V G) + edges G.
Proof.
  unfold edges.
  replace (V (graph_add_point_full G)) with (S (V G)). (* try omega. ne dela zakaj? *)
  - rewrite sum'_S.
    rewrite stozec_edges_part3.
    apply krajsanje.
    apply change_sum.
    intros j p.
    unfold count.
    apply change_sum.
    intros i q.
    (* V naslednji vrstici rewrite; auto dela apply pa ne. *)
    rewrite (stozec_edges_part4 G j p i (Nat.lt_trans i j (V G) q p)); auto.
  - rewrite stozec_ima_tocko_vec.
    (* Moram popraviti definicijo stozca pa bo slo tole brez omega. *)
    omega. 
Qed.
