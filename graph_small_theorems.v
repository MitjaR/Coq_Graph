Require Import Arith.
Require Import Omega.
Require Import Psatz.

Require Import kernel_numeric.
Require Import kernel_graph.
Require Import kernel_graph_extensions.
Require Import graph_examples.
Require Import graph_constructions.

Theorem enakostP2K2:
  graph_equality (K 2) (Path 2).
Proof.
  unfold graph_equality.
  refine (conj _ _). (* Isto kot split. *)
  - auto.
  - intros x p y q.
    replace (V (K 2)) with 2 in *; auto.
    unfold iff.
    split; intro A; simpl; omega. 
    (* replace x with 1; replace y with 0; omega. to prej...*)  
Qed.

Theorem stozec_ponega_polen (n : nat):
  graph_equality (K (n + 1)) (naredi_stozec (K n)).
Proof.
  unfold graph_equality.
  split.
  - rewrite stozec_ima_tocko_vec.
    auto. (* omega tega ne zna auto pa zna *)
  - intros x p y q.
    replace (V (K (n+1))) with (n + 1) in *; auto.
    unfold iff.
    split; intro A; simpl; omega.
Qed.
      