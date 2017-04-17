Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.


(*
Pozor:
Ali je:
le_ge_dec n m : {n <= m} + {n >= m}.
pravilno definiran.
Jaz bi rekel da ne, 
saj moznosti nista izkljucujoce.
*)


(** 
Let us define some graphs. 
**)

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

(* Path on [n] vertices. *)
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

(* [Cycle n] is the cycle on [n+3] vertices. We define it in a way
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


(** 
Graph examples theorems. 
**)

(* Full graph theorems. *)
(*#####>*)
Theorem full_graph_points_number: 
  (forall n : nat, V (K n) = n).
Proof.
  intro.
  auto.
Qed.

Theorem full_graph_edges_number_part (n : nat) :
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


Theorem full_graph_edges_number (n : nat) :
  2 * edges (K n) = n * (n - 1).
Proof.
  rewrite full_graph_edges_number_part.
  rewrite sum_sum_n.
  auto.
Qed.

Theorem full_graph_one_degree_part1 (n : nat) (x : nat) (p : x < n):
  sum' (K n) (fun (i : nat) => if E_decidable (K n) x i then 1 else 0) = 
  sum' (K n) (fun (i : nat) => if Nat.eq_dec x i then 0 else 1).
Proof.
  apply change_sum.
  intros y q.
  set (G := (K n)).
  destruct (E_decidable G x y) as [A|B].
  - destruct (Nat.eq_dec x y) as [C|D].
    + absurd (G x x).
      * now apply E_irreflexive.
      * replace y with x in A. 
        apply A.
    + auto.
  - destruct (Nat.eq_dec x y) as [C|D].
    + auto.
    + absurd (G x y).
      * auto.
      * apply D.
Qed.

Theorem full_graph_one_degree_part2 (n : nat):
  sum n (fun (i : nat) (_ : i < n) => if Nat.eq_dec n i then 0 else 1) =
  sum n (fun (i : nat) (_ : i < n) => 1).
Proof.
  apply change_sum.
  intros j p.
  destruct (Nat.eq_dec n j).
  + absurd (n = j); omega.
  + auto.
Qed.

Theorem full_graph_one_degree (n : nat) (x : nat) (p : x < n):
  degree (K n) x = (n - 1).
Proof.
  unfold degree.
  unfold count.
  rewrite full_graph_one_degree_part1.
  - replace (V (K n)) with n. 
    + induction n.
      * auto. 
      * rewrite sum'_S.
        destruct (Nat.eq_dec x n).
        {
        rewrite Nat.add_0_l.
        unfold sum'.
        replace x with n.
        rewrite full_graph_one_degree_part2.
        pose (sum_n_krat_1 n).
        unfold sum' in e0.
        rewrite e0.
        - omega.
        - auto. (* No tega omega ne zna auto pa zna. *)
        }
        {
        destruct (lt_dec x n).
        - rewrite IHn; omega.
        - omega.
        }
    + auto.
  - auto.
Qed.

Theorem full_graph_sum_degree (n : nat) :
  sum' n (degree (K n)) = n * (n - 1).
Proof.
  unfold sum'.
  replace (sum n (fun (i : nat) (_ : i < n) => degree (K n) i))
    with  (sum n (fun (i : nat) (_ : i < n) => (n - 1))).
  - apply (sum_n_krat_k n (n - 1)).
  - apply change_sum.
    intros j p.
    rewrite (full_graph_one_degree n j); auto.
Qed.

Theorem full_graph_hand_shake (n : nat) :
  2 * edges (K n) = sum' n (degree (K n)).
Proof.
  rewrite full_graph_sum_degree.
  rewrite full_graph_edges_number.
  auto.
Qed.
(*#####<*)
(* Full graph theorems. *)



(* Path theorems. *)
(*#####>*)
Theorem path_points_number: 
  (forall n : nat, V (Path n) = n).
Proof.
  intro.
  auto.
Qed.

Theorem tranzitivnost (n : nat) (x : nat) (y : nat) :
  (y < x /\ x < n -> y < n).
Proof.
  omega.
Qed.


Lemma vsota_funkcij (n : nat) (f g : nat -> nat) :
  sum' n (fun x => (f x) + (g x)) = sum' n f + sum' n g.
Proof.
  induction n.
  - auto.
  - rewrite sum'_S.
    rewrite IHn.
    rewrite sum'_S.
    rewrite sum'_S.
    omega.
Qed.

Theorem path_edges_number_part1 (n : nat) (x : nat) (p : x < n):
  (sum' x (fun y : nat => if E_decidable (Path n) x y then 1 else 0)) =
  (sum' x (fun y : nat => (if Nat.eq_dec x (S y) then 1 else 0))).
Proof.
  apply change_sum.
  intros y q. 
  set (G := (Path n)).
  destruct (E_decidable G x y) as [A|B].
  - destruct A.
    + omega.
    + rewrite H.
      destruct (Nat.eq_dec (S y) (S y)); omega.
  - destruct (Nat.eq_dec x (S y)).
    + absurd (G x y).
      * auto.
      * simpl.
        auto.
    + auto.
Qed.

Theorem path_edges_number_part2 (n : nat) (x : nat) (p : 0 < x < n):
    (sum' x (fun y : nat => (if Nat.eq_dec x (S y) then 1 else 0))) = 1.
Proof.
  induction x.
  - omega.
  - rewrite sum'_S.
    destruct (Nat.eq_dec (S x) (S x)).
    + replace (sum' x (fun y : nat => if Nat.eq_dec (S x) (S y) then 1 else 0)) 
        with 0.
      * omega.
      * replace (sum' x (fun y : nat => if Nat.eq_dec (S x) (S y) then 1 else 0)) 
          with (sum' x (fun y : nat => 0)).
        {
        rewrite (sum_n_krat_k x 0).
        omega.
        }
        {
        apply change_sum'.
        intros j q.
        destruct (Nat.eq_dec (S x) (S j)).
        - omega. 
        - auto.
        }
    + omega.
Qed.

Theorem path_edges_number_part3 (n : nat) :
    (sum' 0 (fun y : nat => (if Nat.eq_dec 0 (S y) then 1 else 0))) = 0.
Proof.
  auto.
Qed.

Theorem path_edges_number_part4 (n : nat) (x : nat) (p : x < n):
  (sum' x (fun y : nat => if E_decidable (Path n) x y then 1 else 0)) = if Nat.eq_dec x 0 then 0 else 1.
Proof.
  (* indukcije se ne rabi uporabil za uporabo primerov *)
  (* ekvivalentno destruct je enako ena ali vecje od ena*)
  induction x. 
  - rewrite path_edges_number_part1.
    + rewrite (path_edges_number_part3 n).
      destruct (Nat.eq_dec 0 0); omega.
    + omega.
  - rewrite path_edges_number_part1.
    + rewrite (path_edges_number_part2 n).
      * destruct (Nat.eq_dec (S x) 0); omega.
      * omega.
    + auto.
Qed.

Theorem path_edges_number_part5 (n : nat):
  (sum (Path n) (fun (i : nat) (_ : i < Path n) =>
     sum' i (fun x : nat => if E_decidable (Path n) i x then 1 else 0))) =
  (sum (Path n) (fun (i : nat) (_ : i < Path n) => if Nat.eq_dec i 0 then 0 else 1)).
Proof.
  apply change_sum'.
  intros j p.
  rewrite (path_edges_number_part4 n j); auto.
Qed.

Theorem path_edges_number (n : nat) :
  edges (Path n) = n - 1.
Proof.
  unfold edges.
  unfold sum'.
  unfold count.
  rewrite (path_edges_number_part5 n).
  replace (V (Path n)) with n.
  - induction n.
    + auto.
    + simpl. 
      rewrite IHn.
      destruct (Nat.eq_dec n 0); omega.
  - auto.
Qed.

(*#####<*)
(* Path theorems. *)

