Require Import Vectors.Vector.
Require Import ZArith.

(*We import the definions and functions we defined for the constraints*)
Require Import constraint.

Import VectorNotations.

(*We dont need to check they have the same length because we use vector*)

Local Open Scope Z_scope.
Local Open Scope vector_scope.

(* Definition of imp_checker and the snd that it works*)
Definition imp_checker {n_v : nat} {n_c : nat }: Type := @constraints n_v n_c -> @constraint n_v -> bool.

Definition imp_checker_snd {n_v : nat} {n_c : nat } (chkr : @imp_checker (S n_v) n_c) : Prop :=
  forall cs c,
    chkr cs c = true ->
    forall (model : @assignment (n_v)), @is_model (S n_v) n_c cs (adapt model) = true -> @is_model_c (S n_v) c (adapt model) = true.


(*Lemma for the soundness of the conic combination of a list of contraints*)
Theorem farkas_equal : forall (n_v n_c : nat) (d : t nat n_c) , @imp_checker_snd n_v n_c (is_equal d).
Proof.
  intros n_v n_c d.
  unfold imp_checker_snd.
  unfold is_equal.
  (*inducción en el número de restricciones*)
  induction n_c as [| n_c' IHn_c'].
  - (*n_c = 0*)
    intros cs c.
    rewrite eqb_eq.
    simpl.
    intro c_is_0.
    replace c with (const 0 (S n_v)).
    unfold is_model_c.
    intro model.
    rewrite eval_0_gt_0.
    reflexivity.
    apply Z.eqb_eq.
  - (*n_c = S n_c'*)
    intros cs c.
    rewrite eqb_eq.
    intro c_is_comb_conic.
    intro model.
    replace c with (comb_conic d cs).
    intro cs_is_model.
    rewrite comb_conic_is_gt.
    reflexivity.
    rewrite cs_is_model.
    reflexivity.
    apply Z.eqb_eq.
Qed.
