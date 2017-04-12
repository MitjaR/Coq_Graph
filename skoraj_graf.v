(** An attempt to formalize graphs. *)

Require Import Arith.
Require Import Psatz.
Require Import Omega.

Require Import dokazanNumerika.

(** Lemma is something that should be proved by others *)

(** In order to avoid the intricacies of constructive mathematics,
    we consider finite simple graphs whose sets of vertices are
    natural numbers 0, 1, , ..., n-1 and the edges form a decidable
    relation.  *)

(** We shall work a lot with statements of the form
    [forall i : nat, i < V -> P i], so we introduce a
    notatation for them, and similarly for existentials. *)
Notation "'all' i : V , P" := (forall i : nat, i < V -> P) (at level 20, i at level 99).
Notation "'some' i : V , P" := (exists i : nat, i < V /\ P) (at level 20, i at level 99).

Structure Graph := {
  V :> nat ; (* The number of vertices. So the vertices are numbers 0, 1, ..., V-1. *)
  E :> nat -> nat -> Prop ; (* The edge relation *)
  E_decidable : forall x y : nat, ({E x y} + {~ E x y}) ;
  E_irreflexive : all x : V, ~ E x x ;
  E_symmetric : all x : V, all y : V, (E x y -> E y x)
}.

Structure Graph' := {
  V' :> nat ; (* The number of vertices. So the vertices are numbers 0, 1, ..., V-1. *)
  E' :> nat -> nat -> bool ; (* The edge relation *)
  E_irreflexive' : all x : V', (E' x x = false) ;
  E_symmetric' : all x : V', all y : V', (E' x y = E' y x)
}.


(** Let us define some graphs. *)

(* Empty graph on [n] vertices *)
Definition Empty (n : nat) : Graph.
Proof.
  refine {| V := n ;
            E := (fun x y => False)
         |} ; auto.
Defined.

(* Complete graph on [n] vertices *)
Definition K (n : nat) : Graph.
Proof.
  refine {| V := n ;
            E := (fun x y => x <> y)
         |}.
  - intros.
    destruct (Nat.eq_dec x y) ; tauto.
  - intros x H L.
    absurd (x = x) ; tauto.
  - intros ; now apply not_eq_sym.
Defined.

(** Path on [n] vertices. *)
Definition Path (n : nat) : Graph.
Proof.
  (* We will do this proof very slowly by hand to practice. *)
  refine {| V := n ;
            E := fun x y => S x = y \/ x = S y
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y).
    + tauto.
    + destruct (eq_nat_dec x (S y)).
      * tauto.
      * { right.
          intros [ ? | ? ].
          - absurd (S x = y) ; assumption.
          - absurd (x = S y) ; assumption.
        }
  - (* This case we do by using a powerful tactic "firstorder".
       We tell it to use the statement [n_Sn] from the [Arith] library.
       To see what [n_Sn] is, run command [Check n_Sn].
       To find [n_Sn], we ran the command [Search (?m <> S ?m)]. *)
    firstorder using n_Sn.
  - intros ? ? ? ? [?|?].
    + right ; now symmetry.
    + left; now symmetry.
Defined.

(** [Cycle n] is the cycle on [n+3] vertices. We define it in a way
    which avoids modular arithmetic. *)
Definition Cycle (n : nat) : Graph.
Proof.
  refine {| V := 3 + n ; (* Do not forget: we have [3+n] vertices 0, 1, ..., n+2 *)
            E := fun x y =>
                 (S x = y \/ x = S y \/ (x = 0 /\ y = 2 + n) \/ (x = 2 + n /\ y = 0))
         |}.
  - intros.
    destruct (eq_nat_dec (S x) y) ;
    destruct (eq_nat_dec x (S y)) ;
    destruct (eq_nat_dec x 0) ;
    destruct (eq_nat_dec y 0) ;
    destruct (eq_nat_dec x (2 + n)) ;
    destruct (eq_nat_dec y (2 + n)) ;
    tauto.
  - intros ? ? H.
    destruct H as [?|[?|[[? ?]|[? ?]]]].
    + firstorder using Nat.neq_succ_diag_l.
    + firstorder using Nat.neq_succ_diag_r.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
    + apply (Nat.neq_succ_0 (S n)) ; transitivity x.
      * now symmetry.
      * assumption.
  - intros ? ? ? ? [?|[?|[[? ?]|[? ?]]]].
    + right ; left ; now symmetry.
    + left ; now symmetry.
    + tauto.
    + tauto.
Defined.

(* We work towards a general theorem: the number of vertices with odd degree is odd. *)

(** Given a decidable predicate [P] on [nat], we can count how many numbers up to [n] satisfy [P]. *)
Definition count (n : nat) {P : nat -> Prop} (decP : forall x, {P x} + {~ P x})  :=
  sum' n (fun x => if decP x then 1 else 0).

(** The number of edges in a graph. *)
Definition edges (G : Graph) : nat :=
  sum' (V G) (fun x => count x (E_decidable G x)).

(* An example: calculate how many edges are in various graphs. *)
Eval compute in edges (Cycle 4). (* NB: This is a cycle on 5 vertices. *)
Eval compute in edges (K 5).
Eval compute in edges (Empty 10).

(** The degree of a vertex. We define it so that it
    return 0 if we give it a number which is not
    a vertex. *)
Definition degree (G : Graph) (x : nat) :=
  count (V G) (E_decidable G x).

(* Let us compute the degree of a vertex. *)

Eval compute in degree (K 6) 3.
Eval compute in degree (Cycle 4) 0.
Eval compute in degree (Cycle 4) 2.

Definition graf_izprazni: Graph -> Graph :=
  fun (G : Graph) => (Empty (V G)).

Definition graf_napolni: Graph -> Graph :=
  fun (G : Graph) => (K (V G)).

Eval compute in graf_izprazni (K 6).
Eval compute in graf_izprazni (Cycle 4).
Eval compute in graf_napolni (Cycle 4).

(*
Definition naredi_mrezo (A : nat * nat) : Graph.
  refine {| V :=  (fst A) * (snd A);
            E := fun x y => x < (snd A) * y \/ y < (snd A) * x
         |}.
  - intros.
*)

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

Theorem stozec_ima_tocko_vec: (forall G : Graph, V (naredi_stozec G) = (V G) +1).
Proof.
  intro.
  auto.
Qed.

Theorem polni_graf_ima_n_tock: (forall n : nat, V (K n) = n).
Proof.
  intro.
  auto.
Qed.

Theorem polni_graf_edges (n : nat) :
  edges (K n) = sum' n (fun x => sum' x (fun y => 1)).
Proof.
  apply change_sum.
  intros x p.
  apply change_sum.
  intros y q.
  destruct (E_decidable (K n) x y) as [_|G].
  - reflexivity.
  - simpl in G.
    omega.
Qed.

Theorem hand_shake (G : Graph) :
  2 * edges G = sum' (V G) (degree G).
Proof.
  unfold edges.

(*
Theorem pot_ima_minus_eno_povezavo: (forall n : nat, edges (Path n) = (V (Path n)) - 1).
Proof.
  intro.
  tauto.



Theorem graf_dodana_tocka_enako_stevilo_povezav: (forall G : Graph, edges (graf_dodana_tocka G) = edges G).
Proof.
  intro.
  tauto.

Theorem stozec_ima_stevilo_tock_vec_povezav: (forall G : Graph, edges (naredi_stozec G) = (edges G) + (V G)).
Proof.
  intro.
*)