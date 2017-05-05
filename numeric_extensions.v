Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.

(**
Sum properties for proving graph theorems.
**)

Lemma sum_i_to_n (n : nat) :
  2 * sum' n (fun i => i) = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl_sum.
    set (y := sum' n (fun x => x)) in *.
    ring_simplify.
    ring_simplify in IHn.
    rewrite IHn.
    nia.
Qed.

Lemma sum_sum_n (n : nat) :
  2 * sum' n (fun x => sum' x (fun y => 1)) = n * (n - 1).
Proof.
  replace (sum' n (fun x => sum' x (fun y => 1))) with 
  (sum' n (fun x => x)).
  - apply sum_i_to_n.
  - apply change_sum'.
    intros j p.
    rewrite sum_n_krat_1.
    + auto.
    + auto.  (* Kaj je to?? *)
Qed.

Theorem zero_is_not_succ (n k l : nat):
    (sum' n (fun y : nat => (if Nat.eq_dec 0 (S y) then k else l))) = n * l.
Proof.
  rewrite (same_sum' n l).
  - auto.
  - intros j p.
    destruct (Nat.eq_dec 0 (S j)); omega.
Qed.

Theorem end_is_not_included (n k l : nat):
    (sum' n (fun y : nat => (if Nat.eq_dec n y then k else l))) = n * l.
Proof.
  rewrite (same_sum' n l).
  - auto.
  - intros j p.
    destruct (Nat.eq_dec n j); omega.
Qed.

Theorem nat_eq_dec_reverse (n k l x : nat):
  (sum' n (fun y : nat => (if Nat.eq_dec x y then k else l))) = 
  (sum' n (fun y : nat => (if Nat.eq_dec y x then k else l))).
Proof.
  apply change_sum.
  intros j p.
  destruct (Nat.eq_dec x j); destruct (Nat.eq_dec j x); omega.
Qed.

Theorem sum_succ_transformation (n k l x: nat) (p: 0 < x < 1 + n):
  sum' n (fun y : nat => if Nat.eq_dec x (S y) then 1 else 0) = 
  sum' n (fun y : nat => if Nat.eq_dec (x - 1) y then 1 else 0).
Proof.
  apply change_sum.
  intros j q.
  destruct (Nat.eq_dec x (S j)); destruct (Nat.eq_dec (x - 1) j); omega.
Qed.

Theorem one_is_found (x y : nat) (p : y < x):
  sum' x (fun x0 : nat => if Nat.eq_dec y x0 then 1 else 0) = 1.
Proof.
  induction x.
  - omega.
  - rewrite sum'_S.
    destruct (Nat.eq_dec y x).
    + assert (sum' x (fun x0 : nat => if Nat.eq_dec y x0 then 1 else 0) =
              sum' x (fun x0 : nat => 0)).
      * apply change_sum.
        intros j q.
        destruct (Nat.eq_dec y j); auto; omega.
      * rewrite (sum_n_krat_k x 0) in H.
        rewrite H.
        omega.
    + rewrite IHx; omega.
Qed.

Theorem one_is_found_general_rv (x y k l : nat) (p : y < x):
  sum' x (fun x0 : nat => if Nat.eq_dec x0 y then k else l) = k + (x - 1) * l.
Proof.
  induction x.
  - omega.
  - rewrite sum'_S.
    destruct (Nat.eq_dec x y).
    + assert (sum' x (fun x0 : nat => if Nat.eq_dec x0 y then k else l) =
              sum' x (fun x0 : nat => l)).
      * apply change_sum.
        intros j q.
        destruct (Nat.eq_dec j y); auto; omega.
      * rewrite (sum_n_krat_k x l) in H.
        rewrite H.
        replace (S x - 1) with x; omega.
    + rewrite IHx.
      (* lia ne zna *)
      (* nia pa zna ze tu*)
      * nia.
      * omega.
Qed.

Theorem one_is_found_general (x y k l : nat) (p : y < x):
  sum' x (fun x0 : nat => if Nat.eq_dec y x0 then k else l) = k + (x - 1) * l.
Proof.
  (*
  assert (k + (x - 1) * l = 
          sum' x (fun x0 : nat => if Nat.eq_dec x0 y then k else l)) as A.
  - rewrite (one_is_found_general_rv); auto.
  - rewrite A.
    apply change_sum.
    intros j q.
    destruct (Nat.eq_dec y j); destruct (Nat.eq_dec j y); omega.
  *)
  rewrite nat_eq_dec_reverse.
  apply one_is_found_general_rv; auto.
Qed.

Theorem one_is_found_rv (x y : nat) (p : y < x):
  sum' x (fun x0 : nat => if Nat.eq_dec x0 y then 1 else 0) = 1.
Proof.
  rewrite (one_is_found_general_rv x y 1 0 p).
  omega.
Qed.

