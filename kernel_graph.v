Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.

Notation "'all' i : V , P" := (forall i : nat, i < V -> P) (at level 20, i at level 99).
Notation "'some' i : V , P" := (exists i : nat, i < V /\ P) (at level 20, i at level 99).

Structure Graph := {
  V :> nat ; (* The number of vertices. So the vertices are numbers 0, 1, ..., V-1. *)
  E :> nat -> nat -> Prop ; (* The edge relation *)
  E_decidable : forall x y : nat, ({E x y} + {~ E x y}) ;
  E_irreflexive : all x : V, ~ E x x ;
  E_symmetric : all x : V, all y : V, (E x y -> E y x)
}.

(** The number of edges in a graph. *)
Definition edges (G : Graph) : nat :=
  sum' (V G) (fun x => count x (E_decidable G x)).

(** The degree of a vertex. We define it so that it
    return 0 if we give it a number which is not
    a vertex. *)
Definition degree (G : Graph) (x : nat) :=
  count (V G) (E_decidable G x).

Theorem edges_symmetry (G : Graph):
  (all x : V G , all y : V G, 
  ((if E_decidable G x y then 1 else 0) = 
  (if E_decidable G y x then 1 else 0))).
Proof.
  intros x p y q.
  destruct (E_decidable G x y); destruct (E_decidable G y x).
  - auto.
  - firstorder using E_symmetric.
  - firstorder using E_symmetric.
  - auto.
Qed.