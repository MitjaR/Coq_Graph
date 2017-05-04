Require Import Arith.
Require Import Omega.
Require Import Psatz.

(* TREBA POPRAVITI KNJIZNICE V COQ!!!*)

(*
Pozor:
Ali je:
le_ge_dec n m : {n <= m} + {n >= m}.
pravilno definiran.
Jaz bi rekel da ne, 
saj moznosti nista izkljucujoce.
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

Definition sum' (n : nat) (f : nat -> nat) := sum n (fun i _ => f i).

(** Given a decidable predicate [P] on [nat], we can count how many numbers up to [n] satisfy [P]. *)
Definition count (n : nat) {P : nat -> Prop} (decP : forall x, {P x} + {~ P x})  :=
  sum' n (fun x => if decP x then 1 else 0).

(* AAA *)
(* verjetno gre v izbiris *)
Definition countA (n : nat) (P : nat -> Prop) (decP : forall x, {P x} + {~ P x}) :=
  sum' n (fun x => if decP x then 1 else 0).

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

Lemma change_sum' (n : nat) (f g : nat -> nat) :
  (forall j (p : j < n), f j = g j) ->
  sum' n f = sum' n g.
Proof.
  unfold sum'.
  apply change_sum.
Qed.

Lemma sum'_S (n : nat) (f : nat -> nat) :
  sum' (S n) f = f n + sum' n f.
Proof.
  unfold sum'.
  reflexivity.
Qed.

Lemma same_sum' (n c : nat) (f : nat -> nat) :
  (forall j (p : j < n), f j = c) ->
  sum' n f = n * c.
Proof.
  induction n.
  - intro H.
    auto.
  - rewrite sum'_S.
    intro H.
    rewrite IHn.
    + rewrite H.
      * lia.
      * omega.
    + auto.
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




(* AAA *)
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

Lemma sum_sum_ULD_part (n : nat) (f : nat -> nat -> nat) :
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

Lemma sum_sum_ULD (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => (sum' x (fun y => f x y))) + 
  sum' n (fun x => (sum' x (fun y => f y x))) + 
  sum' n (fun x => (f x x)) =
  sum' n (fun x => sum' n (fun y => f x y)).
Proof.
  do 2 rewrite vsota_funkcij_rv.
  apply sum_sum_ULD_part.
Qed.


