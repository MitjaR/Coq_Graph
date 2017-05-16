Require Import Arith.
Require Import Omega.
Require Import Psatz.

(* this is for exercise at the moment *)

Theorem double_negation_intrudoction (P : Prop) :
  P -> ~(~ P).
Proof.
  intro A.
  intro B.
  absurd P; auto.
Qed.
(*
Ce se neko trditev lahko dokaze, 
potem ne obstaja dokaz o njeni nedokazljivosti.

Obratno pa ne znamo (double negation elimination)
Ce za neko trditev obstaja dokaz,
da dokaz o njeni nedokazljivosti ne obstaja 
te trditve se vedno ne moremo dokazati.

To je tudi ena pomembnejsih ugotovitev logike.
Obstajajo trditve, ki se jih ne da dokazati niti ovreci.
To je dokazano. Ampak a se to zares lahko dokaze?
*)

Theorem d_n_double_negation_elimination (P : Prop) :
  ~~(~~P -> P).
Proof.
  intro.
  absurd (~P).
  - intro.
    apply H.
    intro.
    absurd (~P); assumption.
  - intro.
    apply H.
    intro.
    assumption.
Qed.

Theorem triple_negation_elimination (P : Prop) :
  ~(~(~ P)) -> ~P.
Proof.
  intro.
  intro.
  absurd P.
  - intro.
    apply H.
    apply double_negation_intrudoction.
    auto.
  - auto.
Qed.

Lemma forall_forall_not (P: nat -> Prop) :
  ~(~(forall x : nat, ~P x)) <-> forall x : nat, ~P x.
Proof.
  split; try tauto.
  intro.
  intro x.
  intro.
  destruct H.
  intro.
  absurd (P x).
  - auto.
  - auto.
Qed.

Theorem absurd_and (A :Prop) :
  ~(A /\ ~A).
Proof.
  intro.
  destruct H.
  absurd A; auto.
Qed.

Theorem double_negated_law_of_excluded_middle (P : Prop) :
  ~~(P \/ (~P)).
Proof.
  intro.
  absurd (~P).
  - intro.
    apply H.
    right.
    assumption.
  - intro.
    apply H.
    left.
    assumption.
Qed.
(*
Posledica: pri danih aksiomih nihce ne more 
imeti dokaza da zakon o izkljuceni tretji 
moznosti ne drzi.

Mi lahko dokazemo da ni dokaza, 
ki bi dokazal da ni dokaza, 
da zakon o izkljuceni tretji moznosti obstaja.
*)

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

Lemma exists_forall_n (P : nat -> Prop):
  ~ (exists x : nat, ~P x) <-> forall x : nat, ~ ~ P x.
Proof.
  split.
  - intro A.
    intro x.
    intro B.
    absurd (exists x : nat, ~P x); auto.
    exists x.
    apply B.
  - intro A.
    intro B.
    destruct B.
    absurd (~P x); auto.
Qed.

Lemma exists_forall_rev (P : nat -> Prop):
  (forall x : nat, ~ P x) <-> ~(exists x : nat, P x).
Proof.
  rewrite (exists_forall P).
  split; auto.
Qed.

(*
Theorem zanikanje_implikacije (A B : Prop):
  (A -> B) <-> (~B -> ~A).
Proof.
  split; try tauto.
  intro.
  intro.
  (* se ne da brez izkljucene tretje moznosti*)
*)  

(*
Theorem law_of_excluded_middle_for_negated_exists (P: nat -> Prop) :
  ~(exists x, P x) \/ ~(~(exists x, P x)).
Proof.
  pose (forall_forall_not P) as A.
  rewrite (exists_forall_rev P) in A.
  assert (~ (exists x : nat, P x) <-> ~ ~ ~ (exists x : nat, P x)).
    - rewrite A; split; auto.
    - do 10 rewrite H.
*)

Lemma exists_nat (P: nat -> Prop) :
  exists x : nat, True.
Proof.
  exists 0; auto.
Qed.

Lemma exists_exists_not (P: nat -> Prop) :
  ~(exists x : nat, ~P x) -> exists x : nat, ~~P x.
Proof.
  rewrite exists_forall_n. (* ta mocnejsa *)
  intro.
  exists 0.
  apply H.
Qed.


(*


(*
to vrjetno ne drzi
Theorem law_of_excluded_middle_propertie (P : Prop) :
  ~P \/ ~(~P) <-> P \/ (~P).
Proof.
  split.
  - intro.
*)

(*
Theorem law_of_excluded_middle_for_negated_prop (P : Prop) :
  ~P \/ ~(~P).
Proof.
  pose (absurd_and P).
*)


(*
Theorem pomozni (A B : Prop) :
  (~A \/ B) <-> (A -> B).
Proof.
  split; try tauto.
*)

Theorem pomozna (A B : Prop) :
  A -> ~(A /\ B) -> ~B.
Proof.
  intros P Q.
  intro.
  auto.
Qed.



Theorem pomoznaC (A B : Prop) :
  (A -> ~B) <-> (B -> ~A).
Proof.
  split; try tauto.
Qed.

Theorem pomoznaD (A B : Prop) :
  (A -> B) -> (~B -> ~A).
Proof.
  tauto.
Qed.




Lemma and_lasnost (A B : Prop) :
  ~(~(~A /\ ~B)) <-> (~A /\ ~B).
Proof.
  tauto.
Qed.

Lemma trikrat (P : Prop) :
  ~(~(~P)) <-> ~P.
Proof.
  tauto.
Qed.

Lemma trikratA (P : Prop) :
  ~(~(~P)) -> ~P.
Proof.
  tauto.
Qed.

Lemma pomozno (P : Prop) :
   ~ (P \/ ~ P) -> P.
Proof.
  intro.
  tauto.
  Show Proof.





  
Lemma forall_exists (P Q: nat -> Prop):
  (forall n : nat, (P n = Q n)) -> ~(exists n : nat, ~(P n = Q n)).
Proof.
  intro.
  intro.
  destruct H0.
  auto.
Qed.
  
  
(*
Theorem multi_de_morgan (f : nat -> Prop) : 
  (forall n : nat, (f n)) -> ~(exists n : nat, ~(f n)).
*)

Theorem de_morgan (A B : Prop) :
  (A /\ B) -> ~(~A \/ ~B).
Proof.
  tauto.
Qed.

Theorem de_morganX (A B : Prop) :
  (~A /\ ~B) <-> ~(A \/ B).
Proof.
  split; try tauto.
Qed.

Theorem de_morganY (A B : Prop) :
  ~(~A /\ ~B) <-> (A \/ B).
Proof.
  split; try tauto.
Qed.


Theorem de_morganX (A B : Prop) :
  (A /\ B) <-> ~(~A \/ ~B).
Proof.
  split; try tauto.
Qed.


*)
