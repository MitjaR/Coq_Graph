Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.

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