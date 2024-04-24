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

Definition cs_imp_c {n_v n_c : nat} (cs : constraints) (c : constraint) : Prop :=
  forall (model : @assignment (n_v)),
    @is_model (S n_v) n_c cs (adapt model) = true -> @is_model_c (S n_v) c (adapt model) = true.

Fixpoint cs_imp_cs' {n_v n_c n_c' : nat} : (@constraints (S n_v) n_c) -> (@constraints (S n_v) n_c') -> Prop :=
  match n_c' with
  | 0%nat => fun _ _ => True
  | S n_c'' => fun cs cs' => cs_imp_c cs (hd cs') /\ cs_imp_cs' cs (tl cs')
  end.

Definition imp_checker_snd {n_v : nat} {n_c : nat } (chkr : @imp_checker (S n_v) n_c) : Prop :=
  forall (cs : constraints) (c : constraint),
    chkr cs c = true ->
     cs_imp_c cs c.


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
  unfold cs_imp_c.
  intros cs c_comb h0 model h1.
  apply (@comb_conic_is_model n_v n_c cs c_comb d model) in h0.
  exact h0.
  exact h1.
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
  forall (cs : constraints) (d : t nat n_c) (c_comb c : @constraint (S n_v)),
    is_equal d cs c_comb = true ->
    forall (model : @assignment n_v), 
    is_model cs (adapt model) = true ->
    is_gt_on_last c_comb c = true ->
    is_model_c c (adapt model) = true.
Proof.
  intros n_v n_c cs d c_comb c.
  intros h0 model h1 h2.
  apply (@comb_conic_is_model n_v n_c cs c_comb d model) in h0.
  apply (@farkas_gt n_v c_comb c model) in h0.
  assumption. assumption. assumption.
Qed.

Definition unsat {n_v n_c : nat} (cs : @constraints (S n_v) n_c) :=
  forall (model : @assignment n_v),
    is_model cs (adapt model) = false.
    
Lemma unsat_suf : forall {n_v n_c : nat} (cs : @constraints (S n_v) n_c) (d : t nat n_c),
    is_minus_one (comb_conic d cs) = true ->
    unsat cs.
Proof.
  intros n_v n_c cs d.
  intro is_minus_one.
  intro model.
  apply (@eval_minus_one n_v (comb_conic d cs) model) in is_minus_one.
  apply is_minus_one_implies in is_minus_one.
  apply if_constraint_lt_0_model_false in is_minus_one.
  exact is_minus_one.
Qed.

(*Lexicographic ranking functions and its definitions*)

(* We are going to represent the lex rank function as a vector of n variables*)


Definition lex_function {n_var : nat} := t Z (S n_var).

Definition from_lex_to_const {n_var : nat} (f : @lex_function n_var) : constraint :=
  let rev_f := (rev f) in
  let const_f := hd rev_f in
  let coef := rev (tl rev_f) in
  coef ++ (const 0 n_var) ++ [const_f].

Definition from_lex_to_const' {n_var : nat} (f : @lex_function n_var) : constraint :=
  let rev_f := (rev f) in
  let const_f := hd rev_f in
  let coef := rev (tl rev_f) in
  (const 0 n_var) ++ (map (fun x => -x) coef) ++ [-const_f].

(*He quereido testar estas funciones pero rev no funciona bien*)

Definition new_constraints {n_v : nat} (c c' : @constraint n_v) : constraints :=
  shiftin c' (shiftin c []).


Require Import List.

Import ListNotations.
Local Open Scope list_scope.

Inductive Lex (cs : constraints) (list_f : list lex_function) : Prop :=
| basic : unsat cs -> (Lex cs []).
| other :
  let f1_x := from_lex_to_const (hd list_f) in
  let f1_x' := from_lex_to_const' (hd list_f) in
  let f1_x'_minus_f1_x := vect_add f1_x f1_x' in
  (Lex (cs ++ f1_x ++ f1_x'_minus_f1_x) (tl list_f)) ->
  (cs_imp_cs' cs (new_constraints f1_x' f1_x'_minus_f1_x)) ->
  Lex cs list_f.
end.

  
