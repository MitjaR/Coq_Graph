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






Definition injektivna_funkcijaA (n : nat) (f : nat -> nat) :=
  all x : n, all y : n, (f x = f y -> x = y).

Definition injektivna_funkcijaB (n : nat) (f : nat -> nat) :=
  all x : n, all y : x, not (f x = f y).

Definition injektivna_funkcijaC (n : nat) (f : nat -> nat) :=
  all x : n, all y : x, (not (x = y) -> not (f x = f y)).

Theorem ekvivalenca_injektivnihAB (n : nat) (f : nat -> nat):
  injektivna_funkcijaA n f <-> injektivna_funkcijaB n f.
Proof.
  unfold injektivna_funkcijaA.
  unfold injektivna_funkcijaB.
  split.
  - intro A.
    intros x p y q.
    intro.
    absurd (x = y).
    + omega.
    + apply A; omega.
  - intro B.
    intros x p y q.
    intro.
    destruct (lt_eq_lt_dec x y) as [[P1|P2]|P3]; auto.
    + absurd (f y = f x); auto.
    + absurd (f x = f y); auto.
Qed.

Theorem ekvivalenca_injektivnihBC (n : nat) (f : nat -> nat):
  injektivna_funkcijaB n f <-> injektivna_funkcijaC n f.
Proof.
  unfold injektivna_funkcijaB.
  unfold injektivna_funkcijaC.
  split.
  - auto.
  - intro C.
    intros x p y q.
    apply C; omega.
Qed.

Structure Bijection (A B : Type) := {
  bij_map :> A -> B ;
  bij_inv : B -> A ;
  bij_inv_right : forall x, bij_map (bij_inv x) = x ;
  bij_inv_left : forall y, bij_inv (bij_map y) = y
}.

Structure Injection (A B : Type) := {
  inj_map :> A -> B ;
  inj_def : forall x y : A, (inj_map x = inj_map y -> x = y) ;
}.

Lemma pomozniA (n : nat) (p : n > 1):
  0 < n.
Proof.
  omega.
Qed.


(**
Pozor:
Kaj vse se v tej definiciji skriva
**)

Definition walk_from_to_with_f_n
  (G : Graph) (x y : nat) (P1 : x < V G) (P2 : y < V G) (n : nat) (P3 : 1 < n) :=
  exists f : nat -> nat, 
  (f 0 = x /\ f (n-1) = y /\ (all j : n-1, G (f j) (f (j + 1)))).

(*
Definition conected_graphD (G : Graph) :
  forall (x : nat) (p : x < (V G)), all y : x, some k : (V G), 
  (k > 1 /\ exists f : (nat -> nat), (walk_from_to_with_f_n G x y p _ k _)).

Definition graph_path_of_n 
  (G : Graph) (n : nat) (p : n > 1) (f : nat -> nat) (Inj_f : injektivna_funkcijaB n f) :=
  (all x : n-1, G (f x) (f (x + 1))).

Definition connected_graphA (G : Graph):
  all x : (V G), all y : x, some k : (V G), (k > 1 /\ exists f : (nat -> nat), 
  (injektivna_funkcijaB k f) /\ f 0 = x /\ f k = y /\ 
  (graph_path_of_n G k _ f _))
refine.
*)



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