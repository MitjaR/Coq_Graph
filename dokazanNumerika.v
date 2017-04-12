Require Import Arith.
Require Import Omega.
Require Import Psatz.

Search ( _ + _ * _).
Search ( _ + 0).
Search ( _ - 0).

Search ( _ + _ - _).
(*
minus_plus_simpl_l_reverse: forall n m p : nat, n - m = p + n - (p + m)
minus_plus: forall n m : nat, n + m - n = m
Nat.add_sub_assoc: forall n m p : nat, p <= m -> n + (m - p) = n + m - p
Nat.add_sub: forall n m : nat, n + m - m = n
Nat.add_sub_swap: forall n m p : nat, p <= n -> n + m - p = n - p + m
*)
Search ( _ * _ - _).
(*
Nat.mul_sub_distr_r: forall n m p : nat, (n - m) * p = n * p - m * p
Nat.mul_sub_distr_l: forall n m p : nat, p * (n - m) = p * n - p * m
*)

Search ( _ + ( _ - _)).
(*
le_plus_minus_r: forall n m : nat, n <= m -> n + (m - n) = m
le_plus_minus: forall n m : nat, n <= m -> m = n + (m - n)
Nat.add_sub_assoc: forall n m p : nat, p <= m -> n + (m - p) = n + m - p
*)


Search (_ + _ = _ + _).

Search (_ <= _ * _).
(*
Nat.mul_le_mono_nonneg_l:
  forall n m p : nat, 0 <= p -> n <= m -> p * n <= p * m
*)
Search (_ <= _ + _).
(*
le_plus_l: forall n m : nat, n <= n + m
le_plus_r: forall n m : nat, m <= n + m
*)
(*
Lemma mnozenje (n : nat) (k : nat):
  ((n + 1) * k = k + n * k).
Proof.
  pose (Nat.mul_add_distr_r n 1 k).
  omega.
Qed.

Lemma kvadrat (n : nat):
  (n * (n - 1)) = (n * n - n).
Proof.
  pose (Nat.mul_sub_distr_l n 1 n).
  omega.
Qed.
*)
  

Fixpoint sum (f : nat -> nat) (n : nat) :=
  match n with
  | 0 => 0
  | S m => f m + sum f m
  end.

Lemma n_manj_n2 (n : nat):
  n <= n * n.
Proof.
  induction n.
  - omega.
  - pose (Nat.mul_add_distr_r n 1 (S n)).
    replace (n+1) with (S n) in e.
    rewrite e.
    + pose (le_plus_r (n * S n) (S n)).
      omega.
    + omega.
Qed.
  (*
  pose (Nat.mul_le_mono_nonneg 1 n n n).
  apply l.
  *)

Lemma asocA (n : nat):
  n + n + (n * n - n) = n + (n + (n * n - n)).
Proof.
  omega.
Qed.


Lemma sum_to_n (n : nat) :
  2 * sum (fun x => x) n = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl.
    set (y := sum (fun x => x) n).
    replace (sum (fun x => x) n) with y in IHn by reflexivity.
    ring_simplify.
    replace (n * (n - 1)) with (n * n - n) in IHn.
    + rewrite IHn.
      rewrite Nat.sub_0_r.
      simpl.
      rewrite Nat.add_0_r.
      (*
      set (x := n * n).
      omega.
      *)
      (*
      pose (le_plus_minus_r n (n*n)).
      *)
      rewrite asocA.
      rewrite (le_plus_minus_r n (n*n)).
      * omega.
      * auto using n_manj_n2.
    + ring_simplify. (* TALE NE ZNA NI SPREMEMBE!*)
      pose (Nat.mul_sub_distr_l n 1 n).
      omega.
Qed.

Lemma sum_y_1_x (x : nat) : 
  (sum (fun y => 1) x = x).
Proof.
  unfold sum.
  induction x.
  - auto.
  - auto.
Qed.

Lemma sum_sum_n2 (n : nat) :
  2 * sum (fun x => (sum (fun y => 1) x)) n = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl.
    set (w :=  sum (fun x : nat => sum (fun _ : nat => 1) x) n).
    replace (sum (fun x : nat => sum (fun _ : nat => 1) x) n) with w in IHn by reflexivity.
    rewrite (sum_y_1_x n). (* TU JE RAZLIKA DOKAZOV *)
    ring_simplify.
    replace (n * (n - 1)) with (n * n - n) in IHn.
    + rewrite IHn.
      rewrite Nat.sub_0_r.
      simpl.
      rewrite Nat.add_0_r.
      rewrite asocA.
      rewrite (le_plus_minus_r n (n*n)).
      * omega.
      * auto using n_manj_n2.
    + pose (Nat.mul_sub_distr_l n 1 n).
      omega.
Qed.
    

Lemma sum_sum_n (n : nat) :
  2 * sum (fun x => (sum (fun y => 1) x)) n = n * (n - 1).
Proof.
  (*
  TO JE NAPAKA!!!
  rewrite sum_y_1_x.
  *)
Admitted.


