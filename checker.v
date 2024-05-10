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


(*This function receives a lex funciton and returns the corresponding constraint*)
Definition c_of_f {n_var : nat} (f : @lex_function n_var) :  @constraint (S (n_var + n_var)) :=
  let rev_f := (rev f) in
  let const_f := hd rev_f in
  let coef := rev (tl rev_f) in
  shiftin const_f (coef ++ (const 0 n_var)).

(*This function receives a lex funciton and returns the corresponding constraint with the signus changed*)
Definition c_of_f' {n_var : nat} (f : @lex_function n_var) :  @constraint (S (n_var + n_var)) :=
  let rev_f := (rev f) in
  let const_f := hd rev_f in
  let coef := rev (tl rev_f) in
  shiftin (-const_f) ((const 0 n_var) ++ (map (fun x => -x) coef)).


(* This function returns the constaint that represent the condition f1(x) - f1(x') >= 0 *)
Definition cs_f_i_minus_f_i' {n_var : nat} (f : @lex_function n_var) : @constraint (S (n_var + n_var)) :=
  vect_add (c_of_f f)  (c_of_f' f).

Definition cs_f_i'_minus_f_i {n_var : nat} (f : @lex_function n_var) : @constraint (S (n_var + n_var)) :=
  vect_mul_Z (-1) (cs_f_i_minus_f_i' f).


(* This function receive a couple of contraint and returns its composition in a constraints*)
Definition new_cs {n_var n_c : nat} (cs : @constraints (S (n_var + n_var)) n_c)  (f : @lex_function n_var) : constraints :=
 shiftin (cs_f_i_minus_f_i' f) (shiftin (cs_f_i'_minus_f_i f) cs).

(*

    list_f = f1::fs ->
     cs => f1>=0 ->
      cs =>f1-f1'>=0 ->
       (Lex f1-f1'<=0::-f1+f1'<=0::cs fs) -> Lex cs list_f
*)

Definition cs_of_two {n_var : nat} (c c' : @constraint n_var) : constraints :=
  shiftin c' (shiftin c []).


Definition cs_f_i_minus_f_i'_is_zero {n_var : nat} (f : @lex_function n_var) :  constraints :=
  cs_of_two (cs_f_i_minus_f_i' f) (cs_f_i'_minus_f_i f).

Definition list_d := list nat.

Require Import List.

Import ListNotations.

Fixpoint is_lex {n_var n_c : nat} (cs : @constraints (S (n_var + n_var)) n_c) (list_f : list (@lex_function n_var)) (list_of_d : list ((list_d)*(list_d))) : bool :=
  match list_f with
  | [] => match list_of_d with
          | [] => false
          | d::ds => let d_i := fst d in
                     let vec_d := of_list d_i in
                     if (length d_i =? n_c)%nat then is_minus_one (comb_conic vec_d cs)
                     else false
          end
  | f::fs =>let f_i := c_of_f f in
            let f_i_minus_f_i' := cs_f_i_minus_f_i' f in
            match list_of_d with
            | [] => false
            | d::ds => ((is_equal (fst d) cs f_i) &&
                          (is_equal (snd d) cs f_i_minus_f_i') &&
                          (is_lex (new_cs cs f) fs ds)
                       )%bool
            end
  end.
 



(*Inductive proposition on the lex functions*)
Inductive Lex {n_var n_c : nat} : (@constraints (S (n_var + n_var)) n_c) -> list (@lex_function n_var) -> Prop :=
| basic
    (cs : (@constraints (S (n_var + n_var)) n_c))
    (list_f : list (@lex_function n_var))
    (H : (length list_f) = 0%nat)
    (H1 : unsat cs)
  : (Lex cs list_f)    
| other
    (cs : (@constraints (S (n_var + n_var)) n_c))
    (list_f : list (@lex_function n_var))
    (f : @lex_function n_var)
    (fs : list (@lex_function n_var))
    (Hl : (length list_f) = S (length fs))
    (H' : list_f = f::fs)
    (H1 : Lex  (new_cs cs f) fs)
    (H2 : cs_imp_cs' cs (cs_f_i_minus_f_i'_is_zero f))
  : (Lex cs list_f).
                                                 
                                                   

