Require Import Arith.
Require Import Omega.
Require Import Psatz.
Require Import Logic.
Require Import Even.

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

Lemma lasnost_vsote2 (n : nat) (f : nat -> nat -> nat) :
  sum' n (fun x => (sum' x (fun y => f x y))) + 
  sum' n (fun x => (sum' x (fun y => f y x))) + 
  sum' n (fun x => (f x x)) =
  sum' n (fun x => sum' n (fun y => f x y)).
Proof.
  do 2 rewrite vsota_funkcij_rv.
  apply lasnost_vsote_part.
Qed.

Lemma test_basic (x : nat):
  True = True.
Proof.
  pose (Nat.Even).
  auto.
Qed.

Definition soda_prica (n k : nat) :=
  n = 2 * k.

Definition liha_prica (n k : nat) :=
  n = 2 * k + 1.

Definition sod (n : nat) :=
  exists k : nat, (soda_prica n k).

Definition lih (n : nat) :=
  exists k : nat, (liha_prica n k).
(*
Lemma even_dec (n : nat):
  {sod n} + {~sod n}.
Proof.
  induction n.
  - left.
    unfold sod.
    exists 0.
    unfold soda_prica.
    auto.
  - destruct IHn. 
    + right.
      unfold sod.
      intro A.
*)
(* tole bi verjetno prestavil sem *)
Definition countA (n : nat) (P : nat -> Prop) (decP : forall x, {P x} + {~ P x}) :=
  sum' n (fun x => if decP x then 1 else 0).

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
Lemma sod_ali_lih (n : nat) :
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

Lemma logika (A B : Prop) :
  (~ A) /\ (A \/ B) -> B.
Proof.
  intro C.
  destruct C.
  destruct H0.
  - absurd A; auto.
  - auto.
Qed.

Lemma logikaA (A B : Prop) :
  (~ A) -> (A \/ B) -> B.
Proof.
  intros P Q.
  destruct Q.
  - absurd A; auto.
  - auto.
Qed.



Lemma sod_ni_lih (n : nat) :
  ~ (Nat.Even n) -> (Nat.Odd n).
Proof.
  intro P.
  apply (logikaA (Nat.Even n)).
  auto.
  apply sod_ali_lih.
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
      pose (sod_ni_lih n).
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
*)
(* logicna posledica sod ni lih... *)
Lemma lih_ni_sod (n : nat) :
  ~ (Nat.Odd n) -> (Nat.Even n).
Proof.
  intro P.
  apply (logikaA (Nat.Odd n)).
  auto.
  (*
  (* assert je ena boljsih stvari *)
  assert (Nat.Even n \/ Nat.Odd n).
  apply sod_ali_lih.
  *)
  pose (sod_ali_lih n).
  tauto.
Qed.

Eval compute in (Datatypes.S 3).

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
      pose (lih_ni_sod n).
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
  pose (sod_ni_lih n).
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
Lemma sod_ni_lihA (n : nat) :
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

Lemma lih_ni_sodA (n : nat) :
  (Nat.Odd n) -> ~(Nat.Even n).
Proof.
  pose (sod_ni_lihA n).
  tauto.
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
    auto; absurd (Nat.Odd (n + m)); try apply (sod_ni_lihA (n + m)); auto.
  - apply sum_odd_part.
    auto.
  - replace (n + m) with (m + n).
    + apply sum_odd_part.
      auto.
    + omega. 
Qed.

Lemma sum_odd_partA (n m : nat):
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
  split; try (apply sum_odd_partA).
  intro Onm.
  destruct (even_odd_dec n); destruct (even_odd_dec m); 
    auto; absurd (Nat.Odd (n + m)); try apply (sod_ni_lihA (n + m)); auto.
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
  countA 0 (fun x : nat => Nat.Odd (f x)) (fun x : nat => odd_dec (f x)) = 0.
Proof.
  auto.
Qed.

Lemma pomoznaA2 (f : nat -> nat):
  sum' 0 f = 0.
Proof.
  auto.
Qed.

(*
Lemma sodo_lihih_v_sodega_part (n : nat) (f : nat -> nat) :
  ((Nat.Even (sum' n f)) -> 
  (Nat.Even (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x)))))
  /\
  ((Nat.Odd (sum' n f)) -> 
  (Nat.Odd (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x))))).
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
  - destruct IHn as [H G].
    split.
    + unfold countA.
      do 2 rewrite sum'_S.
      destruct (odd_dec (sum' n f)) as [A|A].
      * assert (Nat.Odd
          (countA n (fun x : nat => Nat.Odd (f x)) (fun x : nat => odd_dec (f x)))); auto.
        unfold countA in H0.
*)


Lemma sodo_lihih_v_sodega_part (n : nat) (f : nat -> nat) :
  ((Nat.Even (sum' n f)) -> 
  (Nat.Even (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x)))))
  /\
  ((Nat.Odd (sum' n f)) -> 
  (Nat.Odd (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x))))).
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
  - split; unfold countA; do 2 rewrite sum'_S.
    + intro Q.
      rewrite sum_even in Q.
      destruct Q.
      * destruct IHn as [A _].
        assert (Nat.Even
          (countA n (fun x : nat => Nat.Odd (f x)) 
          (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 0.
        {
          apply sum_even_part.
          left.
          unfold countA in H0.
          assert (Nat.Even 0). 
          - unfold Nat.Even; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          pose (sod_ni_lihA (f n)).
          absurd (Nat.Odd (f n)); auto.
        }
      * destruct IHn as [_ A].
        assert (Nat.Odd
          (countA n (fun x : nat => Nat.Odd (f x)) 
          (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 1.
        {
          apply sum_even_part.
          right.
          unfold countA in H0.
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
          (countA n (fun x : nat => Nat.Odd (f x)) 
          (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 0.
        {
          apply sum_odd_partA.
          left.
          unfold countA in H0.
          assert (Nat.Even 0). 
          - unfold Nat.Even; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          pose (sod_ni_lihA (f n)).
          absurd (Nat.Odd (f n)); auto.
        }
      * destruct IHn as [A _].
        assert (Nat.Even
          (countA n (fun x : nat => Nat.Odd (f x)) 
          (fun x : nat => odd_dec (f x)))); destruct H; auto.
        replace (if odd_dec (f n) then 1 else 0) with 1.
        {
          apply sum_odd_partA.
          right.
          unfold countA in H0.
          assert (Nat.Odd 1). 
          - unfold Nat.Odd; exists 0; auto.
          - auto.
        }
        {
          destruct odd_dec; auto.
          absurd (Nat.Odd (f n)); auto.
        }
Qed.


Lemma sodo_lihih_v_sodega (n : nat) (f : nat -> nat) :
  ((Nat.Even (sum' n f)) -> 
  (Nat.Even (countA n (fun x => (Nat.Odd (f x))) (fun x => odd_dec (f x))))).
Proof.
  apply sodo_lihih_v_sodega_part.
Qed.



