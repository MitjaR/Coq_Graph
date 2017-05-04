Require Import Arith.
Require Import Omega.
Require Import Psatz.
Require Import Even.

Require Import kernel_numeric.

Lemma nic_ni_lih (k : nat):
  2 * k + 1 <> 0.
Proof.
  omega.
Qed.

Lemma sod_ni_lih_part (k : nat) :
  (forall l : nat, 2 * l + 1 <> 2 * k).
Proof.
  intro l.
  omega.
Qed.


(** 
Ne strinjam se z definicijo 
Nat.Odd n := exists m : nat, n = 2 * m + 1
Zakaj ni:
Nat.Odd n := exists m : nat, n = 1 + 2 * m

Obrazlozitev:
S (2 * m) = 1 + 2 * m
**)
Lemma even_or_odd (n : nat) :
  (Nat.Even n) \/ (Nat.Odd n).
Proof.
  unfold Nat.Even.
  unfold Nat.Odd.
  induction n.
  - left.
    exists 0.
    auto.
  - destruct IHn.
    + right.
      destruct H as [k G].
      exists k.
      rewrite G.
      omega.
    + left.
      destruct H as [k G].
      exists (S k).
      rewrite G.
      omega.
Qed.

Lemma logika_pom1 (A B : Prop) :
  (~ A) -> (A \/ B) -> B.
Proof.
  intros P Q.
  destruct Q.
  - absurd A; auto.
  - auto.
Qed.



Lemma not_even_is_odd (n : nat) :
  ~ (Nat.Even n) -> (Nat.Odd n).
Proof.
  intro P.
  apply (logika_pom1 (Nat.Even n)).
  auto.
  apply even_or_odd.
Qed.


Lemma exists_forall (P : nat -> Prop):
  ~ (exists x : nat, P x) <-> forall x : nat, ~ P x.
Proof.
  (* firstorder. *)
  split.
  - intro A.
    intro x.
    intro B.
    absurd (exists x : nat, P x); auto.
    exists x.
    apply B.
  - intro A. 
    intro B.
    destruct B.
    absurd (P x); auto.
Qed.

Lemma even_dec : forall n : nat, {Nat.Even n} + {~Nat.Even n}.
Proof.
  intro n.
  induction n.
  - left.
    unfold Nat.Even.
    exists 0.
    omega.
  - destruct IHn.
    + right.
      unfold Nat.Even in e.
      unfold Nat.Even.
      apply exists_forall.
      intro k.
      destruct e.
      rewrite H.
      omega.
    + left.
      pose (not_even_is_odd n).
      assert (Nat.Odd n).
      * auto.
      * unfold Nat.Odd in H.
        destruct H.
        rewrite H.
        unfold Nat.Even.
        exists (S x).
        omega.
Qed.




(*
Search ((_ \/ _) -> (_ \/ _)).
Eval compute in (Datatypes.S 3).
*)
(* logicna posledica not_even_is_odd.. *)
Lemma not_odd_is_even (n : nat) :
  ~ (Nat.Odd n) -> (Nat.Even n).
Proof.
  intro P.
  apply (logika_pom1 (Nat.Odd n)).
  auto.
  (*
  (* assert je ena boljsih stvari *)
  assert (Nat.Even n \/ Nat.Odd n).
  apply sod_ali_lih.
  *)
  pose (even_or_odd n).
  tauto.
Qed.



Lemma odd_dec : forall n : nat, {Nat.Odd n} + {~Nat.Odd n}.
Proof.
  intro n.
  induction n.
  - right.
    unfold Nat.Odd.
    rewrite exists_forall.
    intro x.
    (* tole bi lahko delalo: apply (nic_ni_lih x).  ampak ne dela *)
    pose (nic_ni_lih x).
    omega.
  - destruct IHn as [L|A].
    + right.
      unfold Nat.Odd in *.
      apply exists_forall.
      intro k.
      destruct L.
      rewrite H.
      omega.
    + left.
      pose (not_odd_is_even n).
      assert (Nat.Even n).
      * auto.
      * unfold Nat.Even in H.
        destruct H.
        rewrite H.
        unfold Nat.Odd.
        exists x.
        omega.
Qed.






(* Osnove liho sodo. *)

(**
Na enak nacin bi lahko tudi enega od zgornjih dveh.
Ko imas enega od _dec so ostali enostavni.
**)
Lemma even_odd_dec (n : nat) :
   {Nat.Even n} + {Nat.Odd n}.
Proof.
  destruct (even_dec n); auto.
  pose (not_even_is_odd n).
  auto.
Qed.


Lemma sum_even_part (n m : nat):
  (Nat.Even n /\ Nat.Even m)
  \/
  (Nat.Odd n /\ Nat.Odd m)
  -> 
  Nat.Even (n + m).
Proof.
  intros [[[x H1] [y H2]] | [[x H1] [y H2]]]; unfold Nat.Even in *.
  - exists (x + y).
    rewrite H1.
    rewrite H2.
    omega.
  - exists (1 + x + y).
    rewrite H1.
    rewrite H2.
    omega.
Qed.

Lemma sum_odd_part (n m : nat):
  (Nat.Even n /\ Nat.Odd m)
  -> 
  Nat.Odd (n + m).
Proof.
  intros [[x H1] [y H2]]; unfold Nat.Odd in *.
  - exists (x + y).
    rewrite H1.
    rewrite H2.
    omega.
Qed.


(* poimenovano bolj pravilno. *)
Lemma even_is_not_odd (n : nat) :
  (Nat.Even n) -> ~(Nat.Odd n).
Proof.
  intro P.
  unfold Nat.Odd.
  rewrite exists_forall.
  unfold Nat.Even in *.
  destruct P.
  rewrite H.
  intro.
  omega.
Qed.

Lemma odd_is_not_even (n : nat) :
  (Nat.Odd n) -> ~(Nat.Even n).
Proof.
  pose (even_is_not_odd n).
  (*tauto.*)
  intros A B.
  absurd (Nat.Odd n); auto.
Qed.



Lemma sum_even (n m : nat):
  Nat.Even (n + m) <-> 
  (Nat.Even n /\ Nat.Even m)
  \/
  (Nat.Odd n /\ Nat.Odd m).
Proof.
  split; try (apply sum_even_part).
  intro Snm.
  destruct (even_odd_dec n); destruct (even_odd_dec m); 
    auto; absurd (Nat.Odd (n + m)); try apply (even_is_not_odd (n + m)); auto.
  - apply sum_odd_part.
    auto.
  - replace (n + m) with (m + n).
    + apply sum_odd_part.
      auto.
    + omega. 
Qed.

Lemma sum_odd_part1 (n m : nat):
  (Nat.Even n /\ Nat.Odd m)
  \/
  (Nat.Odd n /\ Nat.Even m)
  -> 
  Nat.Odd (n + m).
Proof.
  intros [[[x H1] [y H2]]|[[x H1] [y H2]]]; unfold Nat.Odd in *;
    exists (x + y); rewrite H1; rewrite H2; omega.
Qed.


(* to je skoraj isti dokaz kot za sode *)
Lemma sum_odd (n m : nat):
  Nat.Odd (n + m) <-> 
  (Nat.Even n /\ Nat.Odd m)
  \/
  (Nat.Odd n /\ Nat.Even m).
Proof.
  split; try (apply sum_odd_part1).
  intro Onm.
  destruct (even_odd_dec n); destruct (even_odd_dec m); 
    auto; absurd (Nat.Odd (n + m)); try apply (even_is_not_odd (n + m)); auto.
  - apply sum_even_part.
    auto.
  - replace (n + m) with (m + n).
    + apply sum_even_part.
      auto.
    + omega. 
Qed.


(* Tole folmulirati je bilo pa kar tezko. *)
(*
Lemma sodo_lihih_v_sodega (n : nat) (f : nat -> nat) :
  (Nat.Even (sum' n f)) -> 
  (Nat.Even (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x)))).
Proof.
*)

Lemma pomoznaA1 (f : nat -> nat):
  count 0 (fun x : nat => odd_dec (f x)) = 0.
Proof.
  auto.
Qed.

Lemma pomoznaA2 (f : nat -> nat):
  sum' 0 f = 0.
Proof.
  auto.
Qed.

Lemma even_odds_in_even_part (n : nat) (f : nat -> nat) :
  ((Nat.Even (sum' n f)) -> 
  (Nat.Even (count n (fun x => odd_dec (f x)))))
  /\
  ((Nat.Odd (sum' n f)) -> 
  (Nat.Odd (count n (fun x => odd_dec (f x))))).
Proof.
  induction n.
  - split; intro.
    + rewrite pomoznaA1.
      auto.
    + rewrite pomoznaA2 in H.
      absurd (Nat.Odd 0); auto; intro.
      unfold Nat.Odd in H.
      destruct H.
      omega.
  - split; unfold count; do 2 rewrite sum'_S.
    + intro Q.
      rewrite sum_even in Q.
      destruct Q.
      * destruct IHn as [A _].
        assert (Nat.Even
          (count n (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 0.
        {
          apply sum_even_part.
          left.
          unfold count in H0.
          assert (Nat.Even 0). 
          - unfold Nat.Even; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          pose (even_is_not_odd (f n)).
          absurd (Nat.Odd (f n)); auto.
        }
      * destruct IHn as [_ A].
        assert (Nat.Odd
          (count n (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 1.
        {
          apply sum_even_part.
          right.
          unfold count in H0.
          assert (Nat.Odd 1). 
          - unfold Nat.Odd; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          absurd (Nat.Odd (f n)); auto.
        }
    + intro Q.
      rewrite sum_odd in Q.
      destruct Q.
      * destruct IHn as [_ A].
        assert (Nat.Odd
          (count n (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 0.
        {
          apply sum_odd_part.
          unfold count in H0.
          assert (Nat.Even 0). 
          - unfold Nat.Even; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          pose (even_is_not_odd (f n)).
          absurd (Nat.Odd (f n)); auto.
        }
      * destruct IHn as [A _].
        assert (Nat.Even
          (count n (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 1.
        {
          apply sum_odd_part1.
          right.
          unfold count in H0.
          assert (Nat.Odd 1). 
          - unfold Nat.Odd; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          absurd (Nat.Odd (f n)); auto.
        }
Qed.

Theorem even_odds_in_even (n : nat) (f : nat -> nat) :
  ((Nat.Even (sum' n f)) -> 
  (Nat.Even (count n (fun x => odd_dec (f x))))).
Proof.
  apply even_odds_in_even_part.
Qed.
