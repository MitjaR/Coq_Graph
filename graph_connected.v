Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_graph.
Require Import graph_examples.
Require Import kernel_numeric.


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

Theorem mini_walk (G : Graph) (n : nat) (p : n > 0) (x y : nat) (Wxy : walk G x y):
  walk_intermediate Wxy = n -> walk G x (walk_func G x y Wxy n).
Proof.
  intro Wxyinl.
  simple refine {| walk_intermediate := (n - 1) ;
                   walk_func := (walk_func G x y Wxy) |}.
  - intros i Ai.
    apply walk_in_graph.
    unfold walk_length.
    rewrite Wxyinl.
    omega.
  - intros i Ai.
    apply walk_connected.
    rewrite Wxyinl.
    omega.
  - apply walk_start.
  - replace (S (n - 1)) with n; auto.
    omega.
Qed.
  




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

(* Search (_ = _). *)




Theorem color_dec (col : nat -> bool) (x : nat):
  {col x = false} + {col x = true}.
Proof.
  destruct (col x); auto.
Qed.

Definition idecomposable (G : Graph) :=
  forall col : nat -> bool, all x : G, all y : G,
  (col x = true -> col y = false ->
   some a : G, some b : G, (col a = true /\ col b = false /\ G a b)).

Theorem change_location_simple1 (n : nat) :
  forall col : nat -> bool,
  (col 0 = true -> col n = false -> 
  some a : n, (col a = true /\ col (S a) = false)).
Proof.
  intros col xCol yCol.
  induction n.
  {
    rewrite yCol in xCol.
    absurd (false = true); auto.
  }
  {
    destruct (color_dec col n).
    - destruct IHn as [a [Aa H]]; auto.
      exists a.
      split.
      + omega.
      + apply H.
    - exists n.
      auto.
  }
Qed.

Theorem change_location_simple2 (n : nat) :
  forall col : nat -> bool,
  (col 0 = false -> col n = true -> 
  some a : n, (col a = false /\ col (S a) = true)).
Proof.
  intros col xCol yCol.
  induction n.
  {
    rewrite yCol in xCol.
    absurd (false = true); auto.
  }
  {
    destruct (color_dec col n).
    - exists n.
      auto.
    - destruct IHn as [a [Aa H]]; auto.
      exists a.
      split.
      * omega.
      * apply H.
  }
Qed.

Theorem change_location_simple1x (x n : nat) (Ax : x < n):
  forall col : nat -> bool,
  (col x = true -> col n = false -> 
  some a : n, (x <= a /\ col a = true /\ col (S a) = false)).
Proof.
  intros col xCol yCol.
  induction n.
  {
    omega.
  }
  {
    destruct (lt_eq_lt_dec x n) as [[H1|H2]|H3].
    {
      destruct (color_dec col n).
      - destruct IHn as [a [Aa H]]; auto.
        exists a.
        split.
        * omega.
        * apply H.
      - exists n.
        split; auto.
        split; auto.
        omega.
    }
    {
      exists x.
      replace x with n in *.
      auto.
    }
    {
      omega.
    }
  }
Qed.

Theorem change_location_simple2x (x n : nat) (Ax : x < n):
  forall col : nat -> bool,
  (col x = false -> col n = true -> 
  some a : n, (x <= a /\ col a = false /\ col (S a) = true)).
Proof.
  intros col xCol yCol.
  induction n.
  {
    omega.
  }
  {
    destruct (lt_eq_lt_dec x n) as [[H1|H2]|H3].
    {
      destruct (color_dec col n).
      - exists n.
        split; auto.
        split; auto.
        omega.
      - destruct IHn as [a [Aa H]]; auto.
        exists a.
        split.
        * omega.
        * apply H.
    }
    {
      exists x.
      replace x with n in *.
      auto.
    }
    {
      omega.
    }
  }
Qed.

Theorem change_location (n : nat): 
  forall col : nat -> bool, all x : n, all y : n,
  (col x = true -> col y = false -> 
   some a : (n - 1), (
  (col a = true /\ col (S a) = false) \/ 
  (col a = false /\ col (S a) = true))).
Proof.
  induction n.
  {
    intros col x Ax y Ay xCol yCol.
    omega.
  }
  {
    intros col x Ax y Ay xCol yCol.
    destruct (lt_eq_lt_dec x y) as [[H1|H2]|H3].
    - pose (change_location_simple1x x y H1 col xCol yCol) as CLS1x.
      destruct CLS1x as [a H].
      destruct H as [Aay [Axa [aCol saCol]]].
      exists a.
      split.
      + omega.
      + auto.
    - replace x with y in *.
      rewrite yCol in xCol.
      absurd (false = true); auto.
    - pose (change_location_simple2x y x H3 col yCol xCol) as CLS2x.
      destruct CLS2x as [a [Aay [Axa [aCol saCol]]]].
      exists a.
      split.
      + omega.
      + auto.
  }
Qed.

Theorem change_location_function (n : nat) (An : n > 1): 
  forall col : nat -> bool, (forall f : nat -> nat,
  col (f 0) = true -> col (f (n-1)) = false -> 
   some a : (n - 1), (
  (col (f a) = true /\ col (f (S a)) = false) \/ 
  (col (f a) = false /\ col (f (S a)) = true))).
Proof.
  intros col f.
  apply (change_location n (fun x => col (f x))); omega.
Qed.


Arguments walk_func {_ _ _} _ _.

Theorem walk_idecomposable 
  (G : Graph) (col : nat -> bool) (x y n : nat) 
  (An : n > 1) (Wxy : walk G x y) :
  walk_length Wxy = n -> 
  (col x = true -> col y = false -> 
   some a : (n - 1), (
  (col ((walk_func Wxy) a) = true /\ col ((walk_func Wxy) (S a)) = false) \/ 
  (col ((walk_func Wxy) a) = false /\ col ((walk_func Wxy) (S a)) = true))).
Proof.
  intros Wxylen xCol yCol.
  apply change_location_function.
  - assumption.
  - replace x with (walk_func Wxy 0) in xCol.
    + assumption.
    + apply walk_start.
  - replace y with (walk_func Wxy (n - 1)) in yCol.
    + assumption.
    + replace (n - 1) with (S (walk_intermediate Wxy)).
      * apply walk_end.
      * rewrite <- Wxylen.
        unfold walk_length.
        omega.
Qed.



Theorem connected_then_idecomposable (G : Graph) : 
  connected G -> idecomposable G.
Proof.
  unfold connected.
  intro Conn.
  unfold idecomposable.
  intros col x xA y yA xCol yCol.
  assert (walk G x y) as Wxy.
  {
    destruct (lt_eq_lt_dec x y) as [[H1|H2]|H3].
    - apply Conn; auto.
    - replace y with x in yCol.
      absurd (col x = true); auto.
      rewrite yCol.
      auto.
    - apply walk_symmetric; auto.
  }
  {
    assert (some a : (walk_length Wxy -1), (
      (col ((walk_func Wxy) a) = true /\ col ((walk_func Wxy) (S a)) = false) \/ 
      (col ((walk_func Wxy) a) = false /\ col ((walk_func Wxy) (S a)) = true))) 
      as H.
    {
      apply walk_idecomposable.
      - unfold walk_length.
        omega.
      - auto.
      - assumption.
      - assumption.
    }
    {
      destruct H as [q [Aq [[H0 H1]|[H2 H3]]]].
      {
        exists (Wxy q).
        split.
        - apply walk_in_graph.
          omega.
        - exists (Wxy (S q)).
          split.
          + apply walk_in_graph.
            omega.
          + split; auto; split; auto.
            apply walk_connected.
            unfold walk_length in Aq.
            omega.
      }
      {
        exists (Wxy (S q)).
        split.
        - apply walk_in_graph.
          omega.
        - exists (Wxy q).
          split.
          + apply walk_in_graph.
            omega.
          + split; auto; split; auto.
            apply (E_symmetric G).
            * apply walk_in_graph.
              omega.
            * apply walk_in_graph.
              omega.
            * apply walk_connected.
              unfold walk_length in Aq.
              omega.
      }
    }
  }
Qed.




Definition increasing_connected_graph (G : Graph) :=
  (forall x : nat, (0 < x < (V G) -> some y : x, (E G x y))).

(*
Theorem increasing_connected_then_connected (G : Graph) :
  increasing_connected_graph G -> connectedA G.
Proof.
  unfold increasing_connected_graph.
  intro ICG.
  unfold connectedA.
  intros x Ax.
  pose (ICG x Ax) as H.
  destruct H.
*)

Definition idecomposableA (G : Graph) :=
  all x : G, all y : G, forall col : nat -> bool,
  (col x = true -> col y = false ->
   some a : G, some b : G, (col a = true /\ col b = false /\ G a b)).

Theorem idecomposable_then_idecomposableA (G : Graph) : 
  idecomposable G -> idecomposableA G.
Proof.
  unfold idecomposable.
  intro Idec.
  unfold idecomposableA.
  intros x Ax y Ay col.
  apply Idec; omega.
Qed.




Theorem idecomposableA_then_someone_to_zero (G : Graph) (y : nat): 
  idecomposableA G -> 
  0 < y < G -> 
  some x : V G, G 0 x.
Proof.
  unfold idecomposableA.
  intros Idec H.
  assert (0 < G) as A0. omega.
  assert (y < G) as Ay. omega.
  set (col := (fun i => match i with
                 | 0 => true
                 | _ => false
               end)).
  assert (col 0 = true) as Col0. auto.
  assert (y <> 0). omega.
  assert (exists y0 : nat, y = S y0). exists (y - 1). omega.
  destruct H1.
  assert (col y = false) as yCol. rewrite H1. auto.
  pose (Idec 0 A0 y Ay col Col0 yCol) as Idec0y.
  destruct Idec0y as [a [Aa [b [Bb K]]]].
  destruct (Nat.eq_dec 0 a).
  - exists b.
    rewrite <- e in K.
    split; auto.
    apply K.
  - absurd (col a = true).
    + assert (a > 0).
      * omega.
      * assert (exists a0 : nat, a = S a0). exists (a - 1). omega.
        destruct H3.
        assert (col a = false). rewrite H3. auto.
        rewrite H4. auto.
    + apply K.
Qed.



Record connected_subgraph (G : Graph) (n : nat) := {
  cs_size := n ;
  cs_col : nat -> bool ;
  cs_size_proof : sum' (V G) (fun x => if cs_col x then 1 else 0) = cs_size ;
  cs_connected_proof : all x : (V G), all y : (V G), (
    cs_col x = true-> cs_col y = true -> walk G x y)
}.

Theorem sum_max_simple (n : nat) (f : nat -> bool) :
  sum' n (fun x => if f x then 1 else 0) <= n.
Proof.
  induction n.
  - auto.
  - rewrite sum'_S.
    assert ((if f n then 1 else 0) <= 1).
    + destruct (f n); omega.
    + omega.
Qed.

Theorem sum_end (n : nat) (f : nat -> bool) 
  (P : sum' n (fun x => if f x then 1 else 0) = n) :
  all y : n, ((fun x => if f x then 1 else 0) y = 1).
Proof.
  induction n.
  {
    intros y Ay.
    omega.
  }
  {
    rewrite sum'_S in P.
    destruct (color_dec f n).
    - destruct (f n).
      + absurd (false = true); auto.
      + pose (sum_max_simple n f).
        absurd (true = true); omega. (* ni v cilju ampak predpostavke *)
    - destruct (f n) in P.
      + assert (sum' n (fun x : nat => if f x then 1 else 0) = n).
        * omega.
        * assert (all y : n, ((if f y then 1 else 0) = 1)) as HH; auto.
          intros y Ay.
          destruct (Nat.eq_dec y n).
          {
            destruct (color_dec f y).
            - rewrite e0 in e1. rewrite e in e1. absurd (false = true); auto.
            - destruct (f y); auto; absurd (false = true); auto.
          }
          {
            apply HH.
            omega.
          }
      + absurd (0 + sum' n (fun x : nat => if f x then 1 else 0) = S n); auto.
        pose (sum_max_simple n f).
        omega.
  }
Qed.

Theorem sum_end_f (n : nat) (f : nat -> bool) 
  (P : sum' n (fun x => if f x then 1 else 0) = n) :
  all y : n, (f y = true).
Proof.
  intros y Ay.
  pose (sum_end n f P y Ay).
  assert ((if f y then 1 else 0) = 1).
  - apply e.
  - destruct (f y); auto.
    omega.
Qed.

Theorem conected_subgraph_connected (G : Graph):
  connected_subgraph G (V G) -> connected G.
Proof.
  intro ConnSub.
  unfold connected.
  intros x y Ax Ay Axy.
  pose (cs_connected_proof G (V G) ConnSub x Ax y Ay) as H.
  pose (cs_size_proof G (V G) ConnSub).
  apply H.
  - apply (sum_end_f (V G)).
    + unfold cs_size in e; auto.
    + apply Ax.
  - apply (sum_end_f (V G)).
    + unfold cs_size in e; auto.
    + apply Ay.
Qed.

Theorem conected_subgraph_extend (G : Graph) (n : nat) (P : 1 + n < (V G)):
  idecomposable G -> connected_subgraph G n -> connected_subgraph G (1 + n).
Proof.
  unfold idecomposable.
  intros Idec ConnSub.
  set (col := (cs_col G n ConnSub)).
  (* sedaj potrebujemo nek x barve true in nek y barve false 
     potem poiscemo vozlisce b in dodamo novo barvo col' 
     ki je enaka povsod razen v vozliscu b je true
     tako smo dobili vecji povezan podgarf
  *)
  pose (Idec col).

Theorem idecomposable_extend (G : Graph) : 
  idecomposable G -> connectedA G.


Theorem idecomposable_then_connectedA (G : Graph) : 
  idecomposable G -> connectedA G.
Proof.
  unfold idecomposable.
  intro Idec.
  unfold connectedA.
  intros x Ax.
  assert (0 < V G) as B0.
  {
    omega.
  }
  {
    assert (x < V G) as Bx.
    - omega.
    - pose (Idec 0 B0 x Bx).
  }



Theorem idecomposable_then_connected (G : Graph) : 
  idecomposable G -> connected G.
Proof.
  unfold idecomposable.
  intro Idec.
  unfold connected.
  intros x y Ax Ay Axy.
















(**

Theorem connected_then_idecomposable (G : Graph) : 
  connected G -> idecomposable G.
Proof.
  unfold connected.
  intro Conn.
  unfold idecomposable.
  intros col x xA y yA xCol yCol.
  assert (walk G x y) as Wxy.
  {
    destruct (lt_eq_lt_dec x y) as [[H1|H2]|H3].
    - apply Conn; auto.
    - replace y with x in yCol.
      absurd (col x = true); auto.
      rewrite yCol.
      auto.
    - apply walk_symmetric; auto.
  }
  {
    set (qqq := walk_intermediate Wxy).
    induction (walk_intermediate Wxy).
    {
    exists x.
    split; auto.
    exists y.
    split; auto.
    split; auto.
    split; auto.
    assert (walk_func Wxy 0 = x).
    - apply walk_start.
    - assert (walk_func Wxy (S (walk_intermediate Wxy)) = y).
      + apply walk_end.
      + assert (walk_intermediate Wxy = 0) as IH0.
        * replace (walk_intermediate Wxy) with qqq; auto.
          admit.
        * rewrite IH0 in H0.
          rewrite <- H. (* to pomeni da naredis revrite H iz druge strani*)
          rewrite <- H0.
          apply walk_connected.
          rewrite IH0.
          auto.
    }
    {

    }
  }
Admitted.











  (col : nat -> bool) (x y : nat) 
  (Ax : x < (V G)) (Ay : y < (V G))
  (xCol : col x = true) (yCol : col y = false) (Wxy : walk G x y):
  (walk_intermediate Wxy = n) ->
  (some i : (walk_length Wxy), 
  ((col (walk_func Wxy i) = true /\ col (walk_func Wxy (S i)) = false) \/
  (col (walk_func Wxy i) = false /\ col (walk_func Wxy (S i)) = true))).
Proof.
  revert Wxy.
  revert yCol xCol Ay Ax.
  revert y.
  unfold walk_length.
  induction n.

Theorem walk_idecomposable (G : Graph) (n : nat) 
  (col : nat -> bool) (x y : nat) 
  (Ax : x < (V G)) (Ay : y < (V G))
  (xCol : col x = true) (yCol : col y = false) (Wxy : walk G x y):
  (walk_intermediate Wxy = n) ->
  (some i : (walk_length Wxy), 
  ((col (walk_func Wxy i) = true /\ col (walk_func Wxy (S i)) = false) \/
  (col (walk_func Wxy i) = false /\ col (walk_func Wxy (S i)) = true))).
Proof.
  revert Wxy.
  revert yCol xCol Ay Ax.
  revert y.
  unfold walk_length.
  induction n.
  

Theorem walk_idecomposable (G : Graph) (n : nat) 
  (col : nat -> bool) (x y : nat) 
  (Ax : x < (V G)) (Ay : y < (V G))
  (AWxy : walk_func Wxy x < walk_func Wxy y)
  (xCol : col x = true) (yCol : col y = false) (Wxy : walk G x y):
  (walk_intermediate Wxy = n) ->
  (some i : (walk_length Wxy), 
  (col (walk_func Wxy i) = true /\ col (walk_func Wxy (S i)) = false)).
Proof.
  revert Wxy.
  revert yCol xCol Ay Ax.
  revert y.
  unfold walk_length.
  induction n.
  {
    intros y yCol xCol Ay Ax.
    intro Wxy.
    intro Wxyinl.
    rewrite Wxyinl.
    exists 0.
    rewrite walk_start.
    split; auto.
    replace 1 with (S (walk_intermediate Wxy)).
    - split; auto.
      rewrite walk_end; auto.
    - rewrite Wxyinl; auto.
  }
  {
    intros y yCol xCol Ay Ax.
    intro Wxy.
    intro Wxyinl.
    rewrite Wxyinl.
    destruct (color_dec col (walk_func Wxy (S n))) as [yPredF|yPredT].
    - (* set (yPred := walk_func Wxy (S (S n))). *)
      assert (walk G x (walk_func Wxy (S n))) as mWxy.
      + {
          simple refine {| walk_intermediate := n;
                           walk_func := (walk_func Wxy) |}.
          - intros i Ai.
            apply walk_in_graph.
            unfold walk_length.
            rewrite Wxyinl.
            omega.
          - intros i Ai.
            apply walk_connected.
            rewrite Wxyinl.
            omega.
          - apply walk_start.
          - omega.
        }
        (*
        apply mini_walk; auto.
        omega.
        *)
      + assert (walk_intermediate mWxy = n) as mWxinl.
        {
          admit.
        }
        {
          assert (some i : S (S (walk_intermediate mWxy)),
                 (col (mWxy i) = true /\ col (mWxy (S i)) = false)).
          * apply IHn; auto.
            {
              apply walk_in_graph.
              unfold walk_length.
              rewrite Wxyinl.
              omega.
            }
            {
              destruct (Nat.eq_dec x (walk_func Wxy (S n))).
              - replace (Wxy (S n)) with x in *.
                rewrite yPredF in xCol.
                absurd (false = true); auto.
              - assert (walk_func Wxy (S (S n)) = y).
                + rewrite <- Wxyinl.
                  apply walk_end.
                + rewrite <- H in Ax.
                  destruct (lt_eq_lt_dec x (Wxy (S n))) as [[H1|H2]|H3]; auto.
                  * absurd (x = Wxy (S n)); auto.
                  * (admited****)
(**
            }
          * rewrite mWxinl in H.
            destruct H as [i [Ai [j [Aj H0]]]].
            exists i.
            split; auto.
            exists j.
            split; auto.
            assert (walk_func mWxy = walk_func Wxy) as same_func.
            {
              admit.
            }
            {
              rewrite same_func in H0.
              auto.
            }
        }
    -
  }


*)
(*
Theorem walk_idecomposable (G : Graph) (*(n : nat)*) (col : nat -> bool) (x y : nat) 
  (Ax : x < (V G)) (Ay : y < (V G)) 
  (Wxy : walk G x y)
  (xCol : col x = true) (yCol : col y = false): 
  (*n = walk_intermediate Wxy ->*)
  (some i : (walk_length Wxy), 
  (some j : (walk_length Wxy), 
  (col (walk_func Wxy i) = true /\ col (walk_func Wxy j) = false))).
Proof.
  unfold walk_length.
  (* pose (walk_end G x y Wxy). *)
  (**intro An.**)
  induction (walk_intermediate Wxy).
  {
    exists 0.
    split; auto.
    rewrite walk_start.
    exists 1.
    split; auto.
    assert (walk_func Wxy 1 = y) as Wf1y.
    - replace 1 with (S (walk_intermediate Wxy)).
      + apply (walk_end G x y Wxy).
      + unfold walk_intermediate.
        admit.
    - rewrite Wf1y.
      auto.
  }
  {

  }











Theorem change_location_functionB (n : nat) (f : nat -> nat): 
  forall col : nat -> bool, all x : n, all y : n,
  (col (f x) = true -> col (f y) = false -> 
   some a : n, (
  (col (f a) = true /\ col (f (S a)) = false) \/ 
  (col (f a) = false /\ col (f (S a)) = true))).
Proof.
  intro col.
  apply (change_location n (fun x => col (f x))).
Qed.

Theorem change_location_functionA (n : nat) : 
  forall col : nat -> bool, all x : n, all y : n,
  (forall f : nat -> nat,
  (col (f x) = true -> col (f y) = false -> 
   some a : n, (
  (col (f a) = true /\ col (f (S a)) = false) \/ 
  (col (f a) = false /\ col (f (S a)) = true)))).
Proof.
  intros col x Ax y Ay f.
  apply change_location_function; auto.
Qed.





(* Search (_ < _).*)

(* Search ((_ < _) -> (_ < _) -> (_ < _)). *)

Arguments walk_func {_ _ _} _ _.

Theorem walk_idecomposable 
  (G : Graph) (col : nat -> bool) (x y n : nat)
  (Ax : x < n) (Ay : y < n) (Wxy : walk G x y) :
  walk_length Wxy = n -> 
  (col ((walk_func Wxy) x) = true -> col ((walk_func Wxy) y) = false -> 
   some a : n, (
  (col ((walk_func Wxy) a) = true /\ col ((walk_func Wxy) (S a)) = false) \/ 
  (col ((walk_func Wxy) a) = false /\ col ((walk_func Wxy) (S a)) = true))).
Proof.
  intro Wxylen.
  apply change_location_functionA; auto.
Qed.

Theorem walk_idecomposableA 
  (G : Graph) (col : nat -> bool) (x y n : nat) (Wxy : walk G x y) :
  walk_length Wxy = n -> 
  (col x = true -> col y = false -> 
   some a : n, (
  (col ((walk_func Wxy) a) = true /\ col ((walk_func Wxy) (S a)) = false) \/ 
  (col ((walk_func Wxy) a) = false /\ col ((walk_func Wxy) (S a)) = true))).
Proof.
  intros Wxylen xCol yCol.
  replace x with (walk_func Wxy 0) in xCol.
  replace y with (walk_func Wxy (S (walk_intermediate Wxy))) in yCol.
  - pose (change_location_functionA (walk_length Wxy) col (Wxy 0)).
Qed.
**)

(*
Theorem idecomposableA_then_someone_to_zero (G : Graph) : 
  idecomposableA G -> 0 < V G -> some x : V G, G 0 x.
Proof.
  unfold idecomposableA.
  intros Idec Ag.
  destruct (lt_eq_lt_dec 0 (V G - 1)) as [[H1|H2]|H3].
  - pose (Idec 0 Ag).
    
  - admit.
  - omega.
  *)