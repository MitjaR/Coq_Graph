Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import graph_examples.
Require Import graph_constructions.

Definition graph_complement (G : Graph) : Graph.
Proof.
  refine {| V := (V G);
            E := fun x y => x <> y  /\ not(E G x y); 
         |}.
  - intros x y.
    destruct (Nat.eq_dec x y).
    + right.
      intro A.
      destruct A.
      auto.
    + destruct (E_decidable G x y).
      * right.
        intro A.
        destruct A.
        auto.
      * auto.
  - intros x q A.
    destruct A.
    auto.
  - intros x q y r.
    pose (E_symmetric G).
    intro A.
    destruct A.
    split; auto. (* spet primer ko auto zna omega pa ne*)
Qed.

Definition ordered_induced_subgraph (G : Graph) (n : nat) (p: n <= (V G)): Graph.
(*Proof. (* kje je Proof. bolj smiselno? *)*)
  refine {| V := n;
            E := fun x y => E G x y; 
         |}.
(* Tu bi sel tudi tukaj ampak kje drugje pa ne saj moti znak ; *)
Proof. 
  - apply (E_decidable G).
  - intros x q.
    apply (E_irreflexive G).
    omega.
  - intros x q y r.
    apply E_symmetric; omega.
Qed.

(* This definition is for reflexive edges only - must be normal graph. *)
Definition graph_equality (G1 : Graph) (G2 : Graph) :=
  (V G1) = (V G2) /\ (all x : (V G1), all y : x, (E G1 x y <-> E G2 x y)).

Definition graph_homomorphism (G1 G2 : Graph) (f : nat -> nat):=
  (all x : (V G1), ((f x) < (V G2)))/\ 
  (all x : (V G1), all y : x, (E G1 x y -> E G2 (f x) (f y))).

(* graph_surjective_homeomorphism *)
Definition graph_epimorphism (G1 G2 : Graph) (f : nat -> nat):=
  (all x : (V G1), ((f x) < (V G2))) /\ 
  (all y : (V G2), some x : (V G1), ((f x) = y)) /\ 
  (all x : (V G1), all y : x, (E G1 x y -> E G2 (f x) (f y))).
(** 
to je sedaj definiran epimorfizm s pripadajoco funkcijo
Mogoce nekoc enako brez da podana funkcija. 
Potem uporabim obstaja f...
**)

Definition graph_monomorphism (G1 G2 : Graph) (f : nat -> nat):=
  (all x : (V G1), ((f x) < (V G2))) /\ 
  (all x1 : (V G1), all x2 : (V G1), ((x1 <> x2) -> ((f x1) <> (f x2)))) /\ 
  (all x : (V G1), all y : x, (E G1 x y -> E G2 (f x) (f y))).

Definition graph_monomorphism_back (G1 G2 : Graph) (f : nat -> nat):=
  (all x : (V G1), ((f x) < (V G2))) /\ 
  (all x1 : (V G1), all x2 : (V G1), ((x1 <> x2) -> ((f x1) <> (f x2)))) /\ 
  (all x : (V G1), all y : x, (E G2 (f x) (f y) -> E G1 x y)).

Definition graph_izomorphismA (G1 G2 : Graph) (f : nat -> nat):=
  (V G1) = (V G2) /\ (graph_epimorphism G1 G2 f).

Definition graph_izomorphismB (G1 G2 : Graph) (f : nat -> nat):=
  (V G1) = (V G2) /\ (graph_monomorphism G1 G2 f).

Definition increasing_conected_graph (G : Graph) :=
  (all x : (V G), some y : x, (E G x y)).

Definition conected_graphA (G : Graph) :=
  (exists H : Graph , ((increasing_conected_graph H) /\ 
   exists f : nat -> nat, (graph_epimorphism H G f))).

(*
Search (~ (_ /\ _) -> (_ \/ _)).
Search (~(_ \/ _) -> (_ /\ _)).
*)



(*
Definition conected_graphB (G : Graph) :=
  (exists H : Graph , ((increasing_conected_graph H) /\ 
   exists f : nat -> nat, (graph_monomorphism_back G H f))).

Definition conected_graphC (G : Graph) :=
  (exists H : Graph , ((increasing_conected_graph H) /\ 
   exists f : nat -> nat, (graph_monomorphism_back 
    (graph_complement G) (graph_complement H) f))).
*)

      
  






