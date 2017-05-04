Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import graph_examples.
Require Import graph_constructions.
 
Definition ordered_induced_subgraph (G : Graph) (n : nat) (p: n <= (V G)): Graph.
  refine {| V := n;
            E := fun x y => E G x y; 
         |}.
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

Definition graph_complement (G : Graph) : Graph.
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

(*
Definition conected_graphB (G : Graph) :=
  (exists H : Graph , ((increasing_conected_graph H) /\ 
   exists f : nat -> nat, (graph_monomorphism_back G H f))).

Definition conected_graphC (G : Graph) :=
  (exists H : Graph , ((increasing_conected_graph H) /\ 
   exists f : nat -> nat, (graph_monomorphism_back 
    (graph_complement G) (graph_complement H) f))).
*)
Theorem enakostP2K2:
  graph_equality (K 2) (Path 2).
Proof.
  unfold graph_equality.
  refine (conj _ _). (* Isto kot split. *)
  - auto.
  - intros x p y q.
    replace (V (K 2)) with 2 in *; auto.
    unfold iff.
    split; intro A; simpl; omega. 
    (* replace x with 1; replace y with 0; omega. to prej...*)  
Qed.

Theorem stozec_ponega_polen (n : nat):
  graph_equality (K (n + 1)) (naredi_stozec (K n)).
Proof.
  unfold graph_equality.
  split.
  - rewrite stozec_ima_tocko_vec.
    auto. (* omega tega ne zna auto pa zna *)
  - intros x p y q.
    replace (V (K (n+1))) with (n + 1) in *; auto.
    unfold iff.
    split; intro A; simpl; omega.
Qed.
      
  

(* 
Hand shaking lemma (Lema o rokovanju):
We work towards a general theorem: 
the number of vertices with odd degree is even. 
*)


(* tole bo kmalu dokazano *)

Lemma lasnost_vsote_rv (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => sum' n (fun y => f x y)) = 
  sum' n (fun x => (sum' x (fun y => f x y))) + 
  sum' n (fun x => (sum' x (fun y => f y x))) + 
  sum' n (fun x => (f x x)).
Proof.
  rewrite sum_sum_ULD.
  auto.
Qed.

Theorem E_irreflexive_grafov (G : Graph):
  all x : (V G), ((if E_decidable G x x then 1 else 0) = 0).
Proof.
  intros x p.
  destruct (E_decidable G x x).
  - pose (E_irreflexive G x p).
    absurd (G x x); auto.
  - auto.
Qed.
  

Theorem hand_shake_pomozna0 (G : Graph):
  sum' G (fun x : nat => if E_decidable G x x then 1 else 0) = 
  sum' G (fun x : nat => 0).
Proof.
  apply change_sum'.
  apply E_irreflexive_grafov.
Qed.

Theorem hand_shake_pomozna1 (G : Graph):
  sum' G (fun x : nat => if E_decidable G x x then 1 else 0) = 0.
Proof.
  rewrite hand_shake_pomozna0.
  rewrite (sum_n_krat_k (V G) 0).
  auto.
Qed.
  

Theorem hand_shake_pomozna2 (G : Graph):
  sum' (V G) (fun x : nat => sum' (V G) (fun y : nat => if E_decidable G x y then 1 else 0)) = 
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G x y then 1 else 0))) +
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G y x then 1 else 0))).
Proof.
  (* uporabim lasnost vsote in pokazem da G x x vedno enako 0*)
  rewrite lasnost_vsote_rv.
  rewrite hand_shake_pomozna1.
  omega.
Qed.

Theorem hand_shake_pomozna3 (G : Graph):
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G x y then 1 else 0))) =
  sum' (V G) (fun x => (sum' x (fun y => if E_decidable G y x then 1 else 0))).
Proof.
  apply change_sum'.
  intros x p.
  apply change_sum'.
  intros y q.
  apply (simetricnost_povezav G x p y (Nat.lt_trans y x (V G) q p)).
Qed.


Theorem hand_shake (G : Graph) :
  2 * edges G = sum' (V G) (degree G).
Proof.
  unfold edges.
  unfold degree.
  unfold count.
  rewrite hand_shake_pomozna2.
  rewrite hand_shake_pomozna3.
  omega.
Qed.




