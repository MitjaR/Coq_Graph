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

(* graph_surjective_homeomorphism *)
Definition graph_epimorphism (G1 G2 : Graph) (f : nat -> nat):=
  (all x : (V G1), ((f x) < (V G2)))/\ (all x : (V G1), all y : x, (E G1 x y -> E G2 (f x) (f y))).
(** 
to je sedaj definiran epimorfizm s pripadajoco funkcijo
Mogoce nekoc enako brez da podana funkcija. 
Potem uporabim obstaja f...
**)


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

(*
Theorem hand_shake (G : Graph) :
  2 * edges G = sum' (V G) (degree G).
*)

