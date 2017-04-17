Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import graph_examples.

(** 
Let us define some graph constructions. 
**)

Definition graf_izprazni: Graph -> Graph :=
  fun (G : Graph) => (Empty (V G)).

Definition graf_napolni: Graph -> Graph :=
  fun (G : Graph) => (K (V G)).

Definition graf_dodana_tocka (G : Graph) :  Graph.
  refine {| V :=  (V G) + 1;
            E := fun x y => x < V G /\ y < V G /\ E G x y
         |}.
  - intros.
    destruct (lt_dec x G) ;
    destruct (lt_dec y G) ;
    destruct (E_decidable G x y) ; tauto.
  - intros x x_lt_G [H1 [H2 H3]].
    destruct (lt_dec x G).
    + absurd (G x x).
      * now apply E_irreflexive.
      * assumption.
    + tauto.
(*   - intros x x_lt_G1 y y_lt_G1 [H1 [H2 H3]].
    firstorder using E_symmetric.
*)
  - intros x xM y yM H.
    destruct H.
    destruct H0.
    split.
    + assumption.
    + split.
      * assumption.
      * now apply E_symmetric.
Defined.

Definition naredi_stozec (G : Graph) :  Graph.
  refine {| V :=  (V G) + 1;
            E := fun x y => (x < V G /\ y < V G /\ E G x y
            ) \/ (x < V G /\ y >= V G) \/ (y < V G /\ x >= V G)
         |}.
  - intros.
    destruct (lt_dec x G).
    + destruct (lt_dec y G).
      * destruct (E_decidable G x y).
        tauto.
        right.
        intro H.
        destruct H.
        tauto.
        destruct H.
        omega.
        omega.
      * left.
        right.
        left.
        omega.
    + destruct (lt_dec y G).
      * left.
        right.
        right.
        omega. 
      * right.
        intro H.
        destruct H.
        tauto.
        tauto.
  - intros.
    intro H0.
    destruct H0.
    + absurd (G x x).
      * now apply E_irreflexive.
      * tauto.
    + omega.
  - intros x xM y yM H.
    destruct H.
    + left. 
      firstorder using E_symmetric.
    + right.
      tauto.
Defined.

(** 
Graph constructions theorems. 
**)

(*
Search (_ + _ = _ + _  -> _ = _).
*)

(* Dodana tocka trditve. *)
(*#####>*)

Theorem graf_dodana_tocka_ima_tocko_vec: (forall G : Graph, V (graf_dodana_tocka G) = (V G) + 1).
Proof.
  intro.
  auto.
Qed.

Theorem graf_dodana_tocka_edges_part1' (G : Graph):
  all x : (V (graf_dodana_tocka G)), 
    ((if (E_decidable (graf_dodana_tocka G) (V (graf_dodana_tocka G)) x) 
    then 1 else 0) = 0).
Proof.
  intros x p.
  destruct (E_decidable (graf_dodana_tocka G) (graf_dodana_tocka G) x).
  - replace (V (graf_dodana_tocka G)) with (S (V G)) in e.
    + destruct e.
      omega.
    + replace (S G) with (G + 1). (* popravi *)
      * apply (graf_dodana_tocka_ima_tocko_vec).
      * omega.
  - auto.
Qed.
      
Theorem graf_dodana_tocka_edges_part1 (G : Graph):
  all x : (V G), 
    ((if (E_decidable (graf_dodana_tocka G) (V G) x) 
    then 1 else 0) = 0).
Proof.
  intros x p.
  destruct (E_decidable (graf_dodana_tocka G) G x).
  - destruct e.
    omega.
  - auto.
Qed.    

Theorem graf_dodana_tocka_edges_part2 (G : Graph):
  count G (E_decidable (graf_dodana_tocka G) G) = 
  sum' G (fun x : nat => 0).
Proof.
  unfold count.
  apply change_sum.
  intros j p.
  pose (graf_dodana_tocka_edges_part1 G j p). (* tu bi rad ' (crtico)*)
  apply e.
Qed.
  
Theorem graf_dodana_tocka_edges_part3 (G : Graph):
  count G (E_decidable (graf_dodana_tocka G) G) = 0.
  rewrite graf_dodana_tocka_edges_part2.
  rewrite (sum_n_krat_k (V G) 0).
  auto.
Qed.


Theorem graf_dodana_tocka_edges_part4 (G : Graph):
  (all x : V G , all y : V G, 
  ((if E_decidable G x y then 1 else 0) =
  (if E_decidable (graf_dodana_tocka G) x y then 1 else 0))).
Proof.
  intros x p y q.
  destruct (E_decidable (graf_dodana_tocka G) x y); destruct (E_decidable G x y); auto.
  - destruct e; absurd (G x y); destruct H0; auto.
  - absurd ((graf_dodana_tocka G) x y). (* Se to da drugace? *)
    + auto.
    + simpl.
      auto.
Qed.

Theorem graf_dodana_tocka_edges (G : Graph): 
  edges (graf_dodana_tocka G) = edges G.
Proof.
  unfold edges.
  replace (V (graf_dodana_tocka G)) with (S (V G)).
  - rewrite sum'_S.
    replace (sum' G (fun x : nat => count x (E_decidable (graf_dodana_tocka G) x))) 
      with (sum' G (fun x : nat => count x (E_decidable G x))).
    + replace (count G (E_decidable (graf_dodana_tocka G) G)) with 0.
      * auto.
      * rewrite graf_dodana_tocka_edges_part3.
        auto.
    + apply change_sum.
      intros j p.
      apply change_sum.
      intros i q.
      (* tega spodaj ne maram inline *)
      (* tegale: (Nat.lt_trans i j (V G) q p) *)
      (* ali se da drugace? *)
      apply (graf_dodana_tocka_edges_part4 G j p i (Nat.lt_trans i j (V G) q p)).
  - replace (S (V G)) with ((V G) + 1). (* popravi!! *)
    + apply (graf_dodana_tocka_ima_tocko_vec G).
    + omega.
Qed.

(*#####<*)
(* Dodana tocka trditve. *)


(* Stozec trditve. *)

Theorem stozec_ima_tocko_vec: (forall G : Graph, V (naredi_stozec G) = (V G) +1).
Proof.
  intro.
  auto.
Qed.

Theorem stozec_edges_part1 (G : Graph):
  all x : (V G), 
    ((if (E_decidable (naredi_stozec G) (V G) x) 
    then 1 else 0) = 1).
Proof.
  intros x p.
  destruct (E_decidable (naredi_stozec G) G x).
  - auto.
  - absurd ((naredi_stozec G) G x).
    + auto.
    + simpl.
      auto. 
Qed.

Theorem stozec_edges_part2 (G : Graph):
  count G (E_decidable (naredi_stozec G) (V G)) = 
  sum' G (fun x : nat => 1).
Proof.
  unfold count.
  apply change_sum.
  intros j p.
  apply (stozec_edges_part1 G j p).
Qed.
  
Theorem stozec_edges_part3 (G : Graph):
  count G (E_decidable (naredi_stozec G) G) = (V G).
  rewrite stozec_edges_part2.
  rewrite (sum_n_krat_k (V G) 1).
  omega.
Qed.

Theorem stozec_edges_part4 (G : Graph):
  (all x : V G , all y : V G, 
  ((if E_decidable G x y then 1 else 0) =
  (if E_decidable (naredi_stozec G) x y then 1 else 0))).
Proof.
  intros x p y q.
  destruct (E_decidable (naredi_stozec G) x y).
  - destruct e; destruct (E_decidable G x y); auto; absurd (G x y); auto.
    + apply H.
    + omega.
  - destruct (E_decidable G x y); auto.
    absurd((naredi_stozec G) x y); auto.
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
  edges (naredi_stozec G) = (V G) + edges G.
Proof.
  unfold edges.
  replace (V (naredi_stozec G)) with (S (V G)). (* try omega. ne dela zakaj? *)
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
