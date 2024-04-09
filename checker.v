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
  forall (cs : constraints) (c : constraint) (model : @assignment (n_v)),
    chkr cs c = true ->
     @is_model (S n_v) n_c cs (adapt model) = true -> @is_model_c (S n_v) c (adapt model) = true.


Lemma comb_conic_is_model : forall {n_v n_c : nat},
  forall (cs : constraints) (c_comb : @constraint (S n_v)) (d : t nat n_c) (model : assignment),
    is_equal d cs c_comb = true ->
    is_model cs (adapt model) = true ->
    is_model_c c_comb (adapt model) = true.
Proof.
  intros n_v n_c cs c_comb d model.
  unfold is_equal.
  (*inducción en el número de restricciones*)
  induction n_c as [| n_c' IHn_c'].
  - (*n_c = 0*)
    rewrite eqb_eq. simpl.
    intro c_is_0.
    replace c_comb with (const 0 (S n_v)).
    unfold is_model_c.
    rewrite eval_0_gt_0.
    reflexivity. apply Z.eqb_eq.
  - (*n_c = S n_c'*)
    rewrite eqb_eq.
    intros c_is_comb_conic.
    replace c_comb with (comb_conic d cs).
    intro cs_is_model.
    rewrite comb_conic_is_gt. reflexivity.
    rewrite cs_is_model. reflexivity.
    apply Z.eqb_eq.
Qed.

(*Lemma for the soundness of the conic combination of a list of contraints*)
Lemma farkas_equal :
  forall (n_v n_c : nat) (d : t nat n_c),
    @imp_checker_snd n_v n_c (is_equal d).
Proof.
  intros n_v n_c d.
  unfold imp_checker_snd.
  intros cs c_comb.
  apply (@comb_conic_is_model n_v n_c cs c_comb d).
Qed.
  
(*Lemma that states that if a constraint satisfies a certain model, then the same
 constraint with greater constant satisfies the same model*)
Lemma farkas_gt : forall {n_v : nat},
  forall (c c' : @constraint (S n_v)) (model : assignment),
    is_model_c c (adapt model) = true
    -> is_gt_on_last c c' = true                                   
    -> is_model_c c' (adapt model) = true.
Proof.
  intros n_v c c' model.
  unfold is_model_c.
  intro is_model_c. rewrite le_snd in is_model_c.
  intro is_gt_on_last_true.
  apply (@eval_is_gt (n_v) c c' (model)) in is_gt_on_last_true.
  rewrite le_snd.
  apply (@Zge_trans (eval c' (adapt model)) (eval c (adapt model)) 0).
  exact is_gt_on_last_true.
  exact is_model_c.
Qed.

Theorem farkas : forall {n_v n_c : nat},
  forall (cs : constraints) (d : t nat n_c) (c_comb c : @constraint (S n_v)) (model : assignment),
    is_equal d cs c_comb = true ->
    is_model cs (adapt model) = true ->
    is_gt_on_last c_comb c = true ->
    is_model_c c (adapt model) = true.
Proof.
  intros n_v n_c cs d c_comb c model.
  intros h0 h1 h2.
  apply (@comb_conic_is_model n_v n_c cs c_comb d model) in h0.
  apply (@farkas_gt n_v c_comb c model) in h0.
  assumption. assumption. assumption.
Qed.

    
Lemma unsat_suf : forall {n_v n_c : nat} (cs : @constraints (S n_v) n_c) (d : t nat n_c),
    is_minus_one (comb_conic d cs) = true ->
    forall (model : @assignment n_v),
    is_model cs (adapt model) = false.
Proof.
  intros n_v n_c cs d.
  intro is_minus_one.
  intro model.
  apply (@eval_minus_one n_v (comb_conic d cs) model) in is_minus_one.
  apply is_minus_one_implies in is_minus_one.
  apply if_constraint_lt_0_model_false in is_minus_one.
  exact is_minus_one.
Qed.
