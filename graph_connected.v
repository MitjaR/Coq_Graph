Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_graph.
Require Import graph_examples.

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

Record path_of_graph (G : Graph) (x y : nat) := {
  path_intermediate : nat ; (* stevilo vmesnih vozlisc *)
  path_length := S (S path_intermediate) ; (* stevilo vozlisc *)
  path_func :> nat -> nat ;
  path_in_graph : forall i, i < path_length -> path_func i < V G ;
  path_connected : forall i, i < S path_intermediate -> G (path_func i) (path_func (S i)) ;
  path_start : path_func 0 = x ;
  path_end : path_func (S path_intermediate) = y;
  path_unique : forall i, i < S path_intermediate -> forall j, j < i -> not (path_func i = path_func j) 
}.

Lemma path_is_walk (G : Graph) (x y : nat) : 
  path_of_graph G x y -> walk G x y.
Proof.
  intro Pxy.
  simple refine {| walk_intermediate := path_intermediate _ _ _ Pxy;
                   walk_func := path_func _ _ _ Pxy |}.
  - apply path_in_graph.
  - apply path_connected.
  - apply path_start.
  - apply path_end.
Qed.

(*
Lemma if_walk_then_path_part (G : Graph) (x y : nat) (P : x < y) (Wxy : walk G x y): 
  exists i, exists j, i < j < S (walk_intermediate Wxy) -> 
  (walk_func G x y Wxy i = walk_func G x y Wxy j /\ forall ii, ii < i -> . 
(* dvakrat injektivnost za vsako stran *)
Proof.
  intros P Wxy.

(* ce lahko do nekam pridemo potem je do tja pot *)
Lemma if_walk_then_path (G : Graph) (x y : nat) : 
  walk G x y -> path_of_graph G x y.
Proof.
  intro Wxy.
*)

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



Lemma walk_symmetric (G : Graph) (x y : nat) :
  x < G -> y < G ->
  walk G x y -> walk G y x.
Proof.
  intros p q Wxy.
  simple refine {|
    walk_intermediate := walk_intermediate Wxy ;
    walk_func := (fun i => Wxy (walk_length Wxy - i - 1))
  |}; unfold walk_length.
  - intros i A.
    apply (walk_in_graph _ _ _ Wxy).
    unfold walk_length.
    omega.
  - intros i A.
    apply E_symmetric.
    + apply (walk_in_graph _ _ _ Wxy); unfold walk_length; omega.
    + apply (walk_in_graph _ _ _ Wxy); unfold walk_length; omega.
    + replace (S (S (walk_intermediate Wxy)) - i - 1) with 
              (S (S (S (walk_intermediate Wxy)) - S i - 1)).
      * apply walk_connected.
        omega.
      * omega.
  - apply walk_end.
  - replace (S (S (walk_intermediate Wxy)) - S (walk_intermediate Wxy) - 1) with 0.
    + apply walk_start.
    + omega.
Qed.

Lemma path_is_connected (n : nat) : connected (Path n).
Proof.
  intros x y xG yG x_lt_y.
  simple refine {| 
    walk_intermediate := y - x - 1;
    walk_func := (fun i => x + i) 
  |}.
  - intros i A.
    omega.
  - intros i A.
    (* zakaj tega noce narediti???
    replace ((Path n) ((fun i0 : nat => x + i0) i) ((fun i0 : nat => x + i0) (S i))) 
      with ((Path n) (x + i) (x + (S i))).
    *)
    (* tega tudi ne.. misli da je to isto?? JA JE ISTO ampak skoda da ne naredi menjave..
    assert (((Path n) (x + i) (x + (S i))) -> 
      ((Path n) ((fun i0 : nat => x + i0) i) ((fun i0 : nat => x + i0) (S i)))).
    *)
    simpl.
    omega.
  - auto. 
  - omega.
Qed.

Definition connectedA (G : Graph) :=
  forall x, 0 < x < G -> walk G 0 x.

Lemma same_conected_zero_or_smallerP2 (G : Graph) :
  connected G -> connectedA G.
Proof.
  unfold connected.
  intro Conn.
  unfold connectedA.
  intros x p.
  apply Conn; omega.
Qed.

Lemma same_conected_zero_or_smallerP1 (G : Graph) :
  connectedA G -> connected G.
Proof.
  unfold connectedA.
  intro ConnA.
  unfold connected.
  intros x y p q w.
  destruct (Nat.eq_dec x 0) as [A|B].
  - rewrite A.
    apply ConnA.
    omega.
  - assert (x > 0). 
    + omega.
    + assert (walk G 0 x).
      * apply ConnA; omega.
      * assert (walk G 0 y).
        {
        apply ConnA; omega.
        }
        {
          assert (walk G x 0).
          - apply walk_symmetric; auto; omega.
          - apply (walk_transitive G x 0 y); auto; omega.
        }
Qed.

Definition connectedB (G : Graph) :=
  forall x y, x < G -> y < G -> not(x = y) -> walk G x y.

Lemma same_conected_smaller_or_allP2 (G : Graph) :
  connectedB G -> connected G.
Proof.
  unfold connectedB.
  intro ConnB.
  unfold connected.
  intros x y xP yP P.
  apply ConnB; omega.
Qed.

(*
Search (_ < _).
*)

Lemma same_conected_smaller_or_allP1 (G : Graph) :
  connected G -> connectedB G.
Proof.
  unfold connected.
  intro Conn.
  unfold connectedB.
  intros x y xP yP P.
  destruct (lt_eq_lt_dec x y) as [[A|B]|C].
  - apply Conn; auto.
  - absurd(x = y); auto.
  - apply walk_symmetric; auto.
Qed.


Definition idecomposable (G : Graph) :=
  forall col : nat -> bool, all x : G, all y : G,
  (col x = true -> col y = false ->
   some a : G, some b : G, (col a = true /\ col b = false /\ G a b)).

Theorem connected_then_idecomposable (G : Graph) : 
  connected G -> idecomposable G.
Proof.
  unfold connected.
  intro Conn.
  unfold idecomposable.
Admitted.

Theorem idecomposable_then_connected (G : Graph) : idecomposable G -> connected G.
Admitted.
