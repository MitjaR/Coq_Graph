Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import graph_examples.


(** 
Graph constructions. 
**)

Definition graph_clear: Graph -> Graph :=
  fun (G : Graph) => (Empty (V G)).

Definition graph_to_full: Graph -> Graph :=
  fun (G : Graph) => (K (V G)).

Definition graph_add_point_clear (G : Graph) :  Graph.
Proof.
  refine {| V :=  1 + (V G);
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

Definition graph_add_point_full (G : Graph) :  Graph.
Proof.
  refine {| V :=  1 + (V G);
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
