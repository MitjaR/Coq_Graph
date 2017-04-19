Require Import Arith.
Require Import Omega.
Require Import Psatz.

(*
(* tole na zalost ni ok *)
Fixpoint sum (n : nat) {struct n} : (forall i, i < n -> nat) -> nat :=
  match n with
  | 0 => (fun f => 0)
  | S m => 
    (fun (f : forall i, i < S m -> nat) => 
      sum m (fun (i : nat) (p : i < m) => 
        f i (Nat.lt_trans i m (S m) p (le_n (S m)))) + f m (le_n (S m)))
  end.

Lemma sum'_S (n : nat) (f : nat -> nat) :
  sum' (S n) f = sum' n f + f n.
Proof.
  reflexivity.
Qed.
*)


(**
Pozor: 
Zaradi definicije naslednika se mora suma odvijati 
po prvem elementu. Sicer povsod problemi z indukcijo.
**)
Fixpoint sum (n : nat) {struct n} : (forall i, i < n -> nat) -> nat :=
  match n with
  | 0 => (fun f => 0)
  | S m => 
    (fun (f : forall i, i < S m -> nat) => 
      f m (le_n (S m)) + 
      sum m (fun (i : nat) (p : i < m) => 
        f i (Nat.lt_trans i m (S m) p (le_n (S m)))))
  end.

Lemma change_sum (n : nat) (f g : forall i, i < n -> nat) :
  (forall j (p : j < n), f j p = g j p) ->
  sum n f = sum n g.
Proof.
  intro E.
  induction n.
  - reflexivity.
  - simpl.
    f_equal.
    + apply E.
    + apply IHn.
      intros j p.
      apply E.
Qed.

Definition sum' (n : nat) (f : nat -> nat) := sum n (fun i _ => f i).


Lemma change_sum' (n : nat) (f g : nat -> nat) :
  (forall j (p : j < n), f j = g j) ->
  sum' n f = sum' n g.
Proof.
  unfold sum'.
  apply change_sum.
Qed.

(*
Lemma sum'_to_sum (n : nat) (f : forall i, i < n -> nat) (g : nat -> nat):
    (forall j (p : j < n), f j p = g j) -> sum' n g = sum n f.
Proof.
  intro.
  unfold sum'.
  apply change_sum.
  auto.
Qed.
*)


Lemma sum'_S (n : nat) (f : nat -> nat) :
  sum' (S n) f = f n + sum' n f.
Proof.
  unfold sum'.
  reflexivity.
Qed.

Ltac simpl_sum :=
  try (rewrite sum'_S in *) ; simpl in *.

Lemma sum_n_krat_k (n : nat) (k : nat):
  sum' n (fun y => k) = n * k.
Proof.
  induction n.
  - auto.
  - simpl_sum.
    rewrite IHn.
    omega.
Qed.

Lemma sum_n_krat_1 (n : nat) (k : nat):
  sum' n (fun y => 1) = n.
Proof.
  rewrite (sum_n_krat_k n 1).
  omega.
Qed.

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

(*
Lemma sum_ind_n_alt1 (n : nat) :
  2 * sum' n (fun x => sum' x (fun y => 1)) = n * (n - 1).
Proof.
  induction n.
  - auto.
  - simpl_sum.
    set (y := sum' n (fun x : nat => sum' x (fun _ : nat => 1))) in *.
    rewrite (sum_n_krat_1 n).
    + ring_simplify.
      ring_simplify in IHn.
      rewrite IHn.
      nia.
    + auto.
Qed.
*)

(**
Tega sedaj verjetno ne bomo rabili.
**)
(*
Lemma basic_minus (n : nat) (m : nat) (k : nat) (p: n >= k):
  n - k + m = n + m - k.
Proof.
  omega. 
Qed.
*)


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

(* 
malo je smesno da rabim tole lemo le da zrcali cez enacaj 
kako se da drugace?
*)
Lemma vsota_funkcij_rv (n : nat) (f g : nat -> nat) :
  sum' n f + sum' n g = sum' n (fun x => (f x) + (g x)).
Proof.
  rewrite vsota_funkcij.
  auto.
Qed.

Lemma krajsanje_izraza (An_ A_n Ann M Q : nat) :
  A_n + M = Q -> An_ + A_n + Ann + M = Ann + An_ + Q.
Proof.
  omega.
Qed.

Lemma lasnost_vsote_part (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => (sum' x (fun y => f x y) + 
                    sum' x (fun y => f y x) + 
                    f x x)) =
  sum' n (fun x => sum' n (fun y => f x y)).
Proof.
  induction n.
  - auto.
  - rewrite sum'_S.
    rewrite IHn.
    rewrite sum'_S.
    rewrite sum'_S.
    set (Ann := f n n).
    set (An_ := sum' n (fun y : nat => f n y)).
    set (A_n := sum' n (fun y : nat => f y n)).
    set (M := sum' n (fun x : nat => sum' n (fun y : nat => f x y))).
    set (Q := sum' n (fun x : nat => sum' (S n) (fun y : nat => f x y))).
    apply (krajsanje_izraza An_ A_n Ann M Q).
    unfold A_n.
    unfold M.
    unfold Q.
    rewrite (vsota_funkcij_rv n 
      (fun y : nat => f y n)
      (fun x : nat => sum' n (fun y : nat => f x y))).
    apply change_sum.
    intros j p.
    rewrite sum'_S.
    auto.
Qed.

Lemma lasnost_vsote (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => (sum' x (fun y => f x y))) + 
  sum' n (fun x => (sum' x (fun y => f y x))) + 
  sum' n (fun x => (f x x)) =
  sum' n (fun x => sum' n (fun y => f x y)).
Proof.
  rewrite vsota_funkcij_rv.
  rewrite vsota_funkcij_rv.
  apply lasnost_vsote_part.
Qed.


