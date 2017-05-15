Require Import kernel_graph.
Require Import graph_examples.
Require Import Omega.

(* A walk in G from x to y. *)
Record walk (G : Graph) (x y : nat) := {
  walk_intermediate : nat ; (* stevilo vmesnih vozlisc *)
  walk_length := S (S walk_intermediate) ; (* stevilo vozlisc *)
  walk_func :> nat -> nat ;
  walk_in_graph : forall i, i < walk_length -> walk_func i < V G ;
  walk_connected : forall i, i < S walk_intermediate -> G (walk_func i) (walk_func (S i)) ;
  walk_start : walk_func 0 = x ;
  walk_end : walk_func (S walk_intermediate) = y
}.

Arguments walk_intermediate {_ _ _} _.
Arguments walk_length {_ _ _} _.

Definition connected (G : Graph) :=
  forall x y, x < G -> y < G -> x < y -> walk G x y.

Lemma prove_for_one (P : nat -> Prop) (i : nat) :
  i < 1 -> P 0 -> P i.
Proof.
  intros H G.
  induction i.
  - assumption.
  - omega.
Qed.

Lemma prove_for_two (P : nat -> Prop) (i : nat) :
  i < 2 -> P 0 -> P 1 -> P i.
Proof.
  intros ilt2 H0 H1.
  induction i.
  - auto.
  - induction i.
    + auto.
    + omega.
Qed.

Lemma complete_connected (n : nat) : connected (K n).
Proof.
  intros x y xG yG x_lt_y.
  simple refine {| walk_intermediate := 0 ;
                   walk_func := (fun i => match i with
                                       | 0 => x
                                       | _ => y
                                       end) |}.
  - intros i H.
    pattern i.
    now apply prove_for_two.
  - intros i H.
    simpl ; pattern i.
    apply prove_for_one.
    + assumption.
    + omega.
  - reflexivity.
  - reflexivity.
Qed.

Lemma walk_transitive (G : Graph) (x y z : nat) :
  x < G -> y < G -> z < G ->
  walk G x y -> walk G y z -> walk G x z.
Proof.
  intros ? ? ? s t.
  assert (E : s (S (walk_intermediate s)) = t 0).
  { rewrite walk_start. apply walk_end. }
  simple refine {|
           walk_intermediate := S (walk_intermediate s + walk_intermediate t) ;
           walk_func := (fun i => if lt_dec i (walk_length s) then s i else t (S (i - walk_length s)))
         |}.
  - intros i ?.
    simpl.
    destruct (lt_dec i (walk_length s)).
    + now apply walk_in_graph.
    + apply walk_in_graph.
      unfold walk_length.
      omega.
  - intros i ? ; simpl.
    destruct (lt_dec i (walk_length s)) ; destruct (lt_dec (S i) (walk_length s)).
    + apply walk_connected.
      unfold walk_length in * ; omega.
    + replace i with (walk_length s - 1) in *.
      * { simpl.
          rewrite Nat.sub_diag.
          rewrite E.
          apply walk_connected.
          omega.
        }
      * omega.
    + omega.
    + unfold walk_length; simpl.
      replace (S (i - S (walk_intermediate s))) with (S (S (i - S (S (walk_intermediate s))))).
      * apply walk_connected.
        unfold walk_length in *.
        omega.
      * unfold walk_length in *.
        omega.
  - now apply walk_start.
  - simpl.
    unfold walk_length in *.
    destruct (lt_dec (S (S (walk_intermediate s + walk_intermediate t))) (S (S (walk_intermediate s)))).
    + omega.
    + rewrite minus_plus.
      apply walk_end.
Defined.

Definition idecomposable (G : Graph) :=
  forall col : nat -> bool, all x : G, all y : G,
  (col x = true -> col y = false ->
   some a : G, some b : G, (col a = true /\ col b = false /\ G a b)).

Theorem connected_then_idecomposable (G : Graph) : connected G -> idecomposable G.
Admitted.

Theorem idecomposable_then_connected (G : Graph) : idecomposable G -> connected G.
Admitted.
