Require Import Arith.
Require Import Omega.
Require Import Psatz.

Fixpoint sum (n : nat) {struct n} : (forall i, i < n -> nat) -> nat :=
  match n with
  | 0 => (fun f => 0)
  | S m =>
    (fun (f : forall i, i < S m -> nat) =>
      sum m (fun (i : nat) (p : i < m) => f i (Nat.lt_trans i m (S m) p (le_n (S m)))) +
      f m (le_n (S m)))
  end.

(*
Fixpoint sum (n : nat) (f : forall i, i < n -> nat) {struct n} : nat.
Proof.
  destruct n.
  - exact 0.
  - simple refine (sum n (fun i (p : i < n) => f i _) + f n _).
    + apply (lt_trans i n (S n)).
      * assumption.
      * auto.
    + auto.
  (* - simple refine (sum n (fun i (p : i < n) => f i _) + f n _) ; omega. *)

  (* - simple refine (_ + _). *)
  (*   + simple refine (sum n (fun i (p : i < n) => f i _)). *)
  (*     * omega. *)
  (*   + simple refine (f n _). *)
  (*     auto. *)
Defined.
*)

Lemma change_sum (n : nat) (f g : forall i, i < n -> nat) :
  (forall j (p : j < n), f j p = g j p) ->
  sum n f = sum n g.
Proof.
  intro E.
  induction n.
  - reflexivity.
  - simpl.
    f_equal.
    + apply IHn.
      intros j p.
      apply E.
    + apply E.
Qed.

Definition sum' (n : nat) (f : nat -> nat) := sum n (fun i _ => f i).

Lemma sum'_S (n : nat) (f : nat -> nat) :
  sum' (S n) f = sum' n f + f n.
Proof.
  reflexivity.
Qed.

Ltac simpl_sum :=
  try (rewrite sum'_S in *) ; simpl in *.

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
  n + 2 * sum' n (fun x => x) = n * n.
Proof.
  induction n.
  - auto.
  - simpl_sum ; lia.
Qed.

Lemma sum_to_n (n : nat) :
  2 * sum' n (fun x => x) = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl_sum.
    set (y := sum' n (fun x => x)) in *.
    (* tu deluje nia. *)
    ring_simplify.
    ring_simplify in IHn.
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
      nia.
    + nia.
Qed.

Lemma sum_y_1_x (n : nat) :
  sum' n (fun y => 1) = n.
Proof.
  induction n.
  - auto.
  - simpl_sum.
    rewrite IHn.
    lia.
Qed.

(*
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
*)



