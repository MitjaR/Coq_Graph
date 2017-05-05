Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import numeric_extensions.
Require Import kernel_graph.
Require Import graph_examples.
Require Import graph_handshake.

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

Theorem full_graph_degree_part1 (n : nat) (x : nat) (p : x < n):
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

Theorem full_graph_degree (n : nat) (x : nat) (p : x < n):
  degree (K n) x = (n - 1).
Proof.
  unfold degree.
  unfold count.
  rewrite (full_graph_degree_part1 n x p).
  rewrite one_is_found_general.
  - replace (V (K n)) with n.
    + omega.
    + auto. (* omega ne zna razbit definicij auto pa *)
  - auto.
Qed.


(* tole ostaja noter samo ker is tega ideja za splosen hand_shake *)
Theorem full_graph_sum_degree (n : nat) :
  sum' n (degree (K n)) = n * (n - 1).
Proof.
  unfold sum'.
  replace (sum n (fun (i : nat) (_ : i < n) => degree (K n) i))
    with  (sum n (fun (i : nat) (_ : i < n) => (n - 1))).
  - apply (sum_n_krat_k n (n - 1)).
  - apply change_sum.
    intros j p.
    rewrite (full_graph_degree n j); auto.
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

Theorem path_edges_number_part2 (n : nat) (x : nat) (p : x < n):
  (sum' x (fun y : nat => if E_decidable (Path n) x y then 1 else 0)) = if Nat.eq_dec x 0 then 0 else 1.
Proof.
  rewrite path_edges_number_part1; auto.
  destruct (Nat.eq_dec x 0) as [A|B].
  - rewrite A.
    apply zero_is_not_succ.
  - rewrite sum_succ_transformation; auto.
    + rewrite one_is_found_general; omega.
    + omega.
Qed.

Theorem path_edges_number_part3 (n : nat):
  (sum' (Path n) (fun (i : nat) =>
     sum' i (fun x : nat => if E_decidable (Path n) i x then 1 else 0))) =
  (sum' (Path n) (fun (i : nat) => if Nat.eq_dec i 0 then 0 else 1)).
Proof.
  apply change_sum'.
  intros j p.
  rewrite (path_edges_number_part2 n j); auto.
Qed.

Theorem path_edges_number (n : nat) :
  edges (Path n) = n - 1.
Proof.
  unfold edges.
  unfold count.
  rewrite (path_edges_number_part3 n).
  replace (V (Path n)) with n.
  - induction n.
    + auto.
    + simpl.
      rewrite sum'_S.
      rewrite IHn.
      destruct (Nat.eq_dec n 0); omega.
  - auto.
Qed.
(*#####<*)
(* Path theorems. *)


(* Cycle theorems. *)
(*#####>*)
Theorem cycle_points_number (n : nat):
  V (Cycle n) = 3+n.
Proof.
  auto.
Qed.

Theorem cycle_edges_number_part1 (n : nat) (x : nat) (p : x < 2+n):
  (sum' x (fun y : nat => if E_decidable (Cycle n) x y then 1 else 0)) =
  (sum' x (fun y : nat => (if Nat.eq_dec x (S y) then 1 else 0))).
Proof.
  apply change_sum.
  intros y q. 
  set (G := (Cycle n)).
  destruct (E_decidable G x y) as [A|B].
  - destruct A as [[H1|H2]|[H3|H4]]; try omega.
    rewrite H2.
    destruct (Nat.eq_dec (S y) (S y)); omega.
  - destruct (Nat.eq_dec x (S y)); auto.
    absurd (G x y); auto.
    simpl.
    auto.
Qed.
  
Theorem cycle_edges_number_part2 (n : nat) (x : nat) (p : x < 2+n):
  (sum' x (fun y : nat => if E_decidable (Cycle n) x y then 1 else 0))=if Nat.eq_dec x 0 then 0 else 1.
Proof.
  rewrite cycle_edges_number_part1; auto.
  destruct (Nat.eq_dec x 0) as [A|B].
  - rewrite A.
    apply zero_is_not_succ.
  - rewrite sum_succ_transformation; auto.
    + rewrite one_is_found_general; omega.
    + omega.
Qed.

Theorem cycle_edges_number_part3 (n : nat) (x : nat) (p : x = 2+n):
  (sum' x (fun y : nat => if E_decidable (Cycle n) x y then 1 else 0)) =
  (sum' x (fun y : nat => (if Nat.eq_dec 0 y then 1 else 0) + (if Nat.eq_dec (1+n) y then 1 else 0))).
Proof.
  apply change_sum.
  intros y q. 
  set (G := (Cycle n)).
  destruct (E_decidable G x y) as [A|B].
  - destruct A as [[H1|H2]|[H3|H4]]; try omega.
    + assert (y = S n).
      * omega.
      * rewrite H.
        destruct (Nat.eq_dec 0 (S n)); destruct (Nat.eq_dec (1+n) (S n)); auto; omega.
    + destruct H4 as [_ w].
      rewrite w.
      destruct (Nat.eq_dec 0 0); destruct (Nat.eq_dec (1+n) 0); auto; omega.
  - destruct (Nat.eq_dec 0 y); destruct (Nat.eq_dec (1+n) y); auto; try omega.
    + absurd (G x y); auto; simpl; auto.
    + absurd (G x y); auto; simpl; left; right; omega.
Qed.

Theorem cycle_edges_number_part4 (n : nat) (x : nat) (p : x < 3+n):
  (sum' x (fun y : nat => if E_decidable (Cycle n) x y then 1 else 0))=
  (if Nat.eq_dec x (2+n) then 1 else 0) + (if Nat.eq_dec x 0 then 0 else 1).
Proof.
  destruct (Nat.eq_dec x (2+n)) as [A|B].
  - rewrite (cycle_edges_number_part3 n x A).
    rewrite vsota_funkcij.
    assert (q : 0 < x).
    + omega.
    + rewrite (one_is_found x 0 q).
      assert (w : (1+n) < x).
      * omega.
      * rewrite (one_is_found x (1+n) w).
        destruct (Nat.eq_dec x 0); omega.
  - apply cycle_edges_number_part2.
    omega.
Qed.

Theorem cycle_edges_number (n : nat):
  edges (Cycle n) = 3+n.
Proof.
  unfold edges.
  assert (sum' (Cycle n) (fun x : nat => count x (E_decidable (Cycle n) x)) =
         (sum' (Cycle n) (fun x : nat => 
            (if Nat.eq_dec x (2+n) then 1 else 0) + (if Nat.eq_dec x 0 then 0 else 1)))).
  - apply change_sum.
    intros x p.
    unfold count.
    apply cycle_edges_number_part4.
    auto.
  - rewrite H.
    rewrite vsota_funkcij.
    replace (V (Cycle n)) with (3+n); auto.
    assert (q : (2 + n) < (3 + n)).
    + omega.
    + rewrite (one_is_found_rv (3 + n) (2 + n) q).
      assert (p : 0 < (3 + n)).
      * omega.
      * rewrite (one_is_found_general_rv (3 + n) 0 0 1 p).
        omega.
Qed.


Theorem cycle_point_degree_part1 (n x y : nat) (p : x < 3+n) (q : y < 3+n):
  (if E_decidable (Cycle n) x y then 1 else 0) = 
  (if (eq_nat_dec (S x) y) then 1 else 0) +
  (if (eq_nat_dec x (S y)) then 1 else 0) +
  (if (eq_nat_dec x 0) then (if (eq_nat_dec y (2 + n)) then 1 else 0) else 0) +
  (if (eq_nat_dec y 0) then (if (eq_nat_dec x (2 + n)) then 1 else 0) else 0).
Proof.
  destruct (eq_nat_dec (S x) y);
  destruct (eq_nat_dec x (S y)); try omega;
  destruct (eq_nat_dec x 0); destruct (eq_nat_dec y (2 + n));
  destruct (eq_nat_dec y 0); destruct (eq_nat_dec x (2 + n));
  try omega;
  destruct (E_decidable (Cycle n) x y) as [A|B];
  try omega; 
  try destruct A; try omega; absurd ((Cycle n) x y); auto; simpl; auto.
  (*
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - destruct A; omega.
  - destruct A; omega.
  - destruct A; omega.
  - destruct A; omega.
  - absurd ((Cycle n) x y); auto; simpl; auto.
  - destruct A; omega.
  - destruct A; omega.
  - destruct A; omega.
  *)
Qed.

Theorem cycle_point_degree_part2 (n x : nat) (p : x < 3+n):
  sum' (3 + n) (fun y : nat => 
  if E_decidable (Cycle n) x y then 1 else 0) = 
  sum' (3 + n) (fun y : nat => 
  (if (eq_nat_dec (S x) y) then 1 else 0) +
  (if (eq_nat_dec x (S y)) then 1 else 0) +
  (if (eq_nat_dec x 0) then (if (eq_nat_dec y (2 + n)) then 1 else 0) else 0) +
  (if (eq_nat_dec y 0) then (if (eq_nat_dec x (2 + n)) then 1 else 0) else 0)).
Proof.
  apply change_sum.
  intros y q.
  apply cycle_point_degree_part1; auto.
Qed.

Theorem cycle_point_degree_part3 (n x : nat) (p : x < 3+n):
  sum' (3 + n) (fun y : nat => 
  (if (eq_nat_dec (S x) y) then 1 else 0) +
  (if (eq_nat_dec x (S y)) then 1 else 0) +
  (if (eq_nat_dec x 0) then (if (eq_nat_dec y (2 + n)) then 1 else 0) else 0) +
  (if (eq_nat_dec y 0) then (if (eq_nat_dec x (2 + n)) then 1 else 0) else 0)) = 2.
Proof.
  do 3 rewrite vsota_funkcij.
  destruct (Nat.eq_dec x 0); destruct (Nat.eq_dec x (2 + n)).
  - omega.
  - assert (2 + n < 3 + n) as w; try omega.
    rewrite (one_is_found_rv (3 + n) (2 + n) w).
    assert ((S x) < 3 + n) as q; try omega.
    rewrite (one_is_found (3 + n) (S x) q).
    rewrite (same_sum' (3 + n) 0). 
    + rewrite (same_sum' (3 + n) 0).
      * omega.
      * intros j g1.
        destruct (Nat.eq_dec j 0); auto.
    + intros j g1.
      destruct (Nat.eq_dec x (S j)); auto.
      omega.
  - assert (0 < 3 + n) as q; try omega.
    rewrite (one_is_found_rv (3 + n) 0 q).
    rewrite (sum_n_krat_k (3 + n) 0).
    rewrite (same_sum' (3 + n) 0).
    + replace (sum' (3 + n) (fun x0 : nat => if Nat.eq_dec x (S x0) then 1 else 0))
        with (sum' (3 + n) (fun x0 : nat => if Nat.eq_dec (x-1) x0 then 1 else 0)).
      * assert (x - 1 < 3 + n) as w; try omega.
        rewrite (one_is_found (3 + n) (x - 1) w).
        omega.
      * apply change_sum.
        intros j g1.
        destruct (Nat.eq_dec x (S j)); destruct (Nat.eq_dec (x - 1) j); omega.
    + intros j g1.
      destruct (Nat.eq_dec (S x) j); omega.
  - rewrite (sum_n_krat_k (3 + n) 0).
    assert ((S x) < 3 + n) as q; try omega.
    rewrite (one_is_found (3 + n) (S x) q).
    replace (sum' (3 + n) (fun x0 : nat => if Nat.eq_dec x (S x0) then 1 else 0))
      with (sum' (3 + n) (fun x0 : nat => if Nat.eq_dec (x-1) x0 then 1 else 0)).
    + assert (x - 1 < 3 + n) as w; try omega.
      rewrite (one_is_found (3 + n) (x - 1) w).
      rewrite (same_sum' (3 + n) 0).
      * omega.
      * intros j g1.
        destruct (Nat.eq_dec j 0); omega.
    + apply change_sum.
      intros j g1.
      destruct (Nat.eq_dec x (S j)); destruct (Nat.eq_dec (x - 1) j); omega.
Qed.

Theorem cycle_point_degree (n : nat):
  forall (x : nat),  x < 3 + n -> (degree (Cycle n) x = 2).
Proof.
  intros x p.
  unfold degree.
  unfold count.
  replace (V (Cycle n)) with (3+n); auto.
  set (G := Cycle n).
  rewrite cycle_point_degree_part2; auto.
  rewrite cycle_point_degree_part3; auto.
Qed.

Theorem cycle_edges_number' (n : nat):
  2 * edges (Cycle n) = 6 + 2 * n.
Proof.
  rewrite handshake.
  assert (sum' (Cycle n) (degree (Cycle n)) = sum' (Cycle n) (fun x => 2)) as A.
  - apply change_sum.
    apply cycle_point_degree.
  - rewrite A.
    rewrite sum_n_krat_k.
    simpl.
    omega.
Qed.

(*#####<*)
(* Cycle theorems. *)

