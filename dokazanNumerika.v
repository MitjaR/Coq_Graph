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


Fixpoint sum' (n : nat) (f : forall i, i < n -> nat) {struct n} : nat.
Proof.
  destruct n.
  - exact 0.
  - simple refine (sum' n (fun i (p : i < n) => f i _) + f n _).
    + apply (lt_trans i n (S n)).
      * assumption.
      * auto.
    + auto.
  (* - simple refine (sum' n (fun i (p : i < n) => f i _) + f n _) ; omega. *)

  (* - simple refine (_ + _). *)
  (*   + simple refine (sum' n (fun i (p : i < n) => f i _)). *)
  (*     * omega. *)
  (*   + simple refine (f n _). *)
  (*     auto. *)
Defined.

Definition sum (n : nat) (f : nat -> nat) := sum' n (fun i _ => f i).

Lemma asocA (n : nat):
  n + n + (n * n - n) = n + (n + (n * n - n)).
Proof.
  omega.
Qed.

Lemma n_manj_n2 (n : nat):
  n <= n * n.
Proof.
  nia.
Qed.

Lemma sum_to_n' (n : nat) :
  n + 2 * sum n (fun x => x) = n * n.
Proof.
  induction n.
  - auto.
  - simpl in *.
Qed.

Lemma sum_to_n (n : nat) :
  2 * sum n (fun x => x) = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl.
    set (y := sum n (fun x => x)) in *.
    (* tu deluje nia. *)
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

Lemma sum_y_1_x (n : nat) :
  sum n (fun y => 1) = n.
Proof.
  unfold sum ; induction n ; auto.
Qed.

Lemma sum_sum_n2 (n : nat) :
  2 * sum n (fun x => sum x (fun y => 1) x) = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl.
    set (w :=  sum n (fun x : nat => sum x (fun _ : nat => 1))) in *.
    rewrite sum_y_1_x. (* TU JE RAZLIKA DOKAZOV *)
    (* na tem mestu deluje: nia. *)
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



