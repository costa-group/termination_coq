Require Import Vectors.Vector.
Require Import ZArith.

Import VectorNotations.

(*Definitions*)

Definition constraint {n_v : nat} : Type := t Z n_v.

Definition constraints {n_v : nat} {n_c : nat } : Type := t (@constraint n_v) n_c.

(*When defining a model we should allways add a 1 at the end*)
Definition assignment { n : nat} : Type := t Z n.

(*We dont need to check they have the same length because we use vector*)

Local Open Scope Z_scope.
Local Open Scope vector_scope.

(*Functions*)

(*Given an inequation and a map of values (x_i -> m_i) we subtitute those at the inequation*)
Fixpoint eval {n : nat} : @constraint n -> @assignment n -> Z :=
  match n with
  | 0%nat => fun _ _ => 0
  | S n' => fun c m => (hd c) * (hd m) + eval (tl c) (tl m)
  end.

Example test_eval :  eval [1; 2; 3] [1; 2; 3] = 14.
Proof. reflexivity. Qed.

(* Checks wether or not a certain constraint and model are greater than zero*)
Definition is_model_c {n : nat} (c : @constraint n) (model : @assignment n) : bool :=
  (eval c model) >=? 0.

Example test_is_model_c : is_model_c  [1; 2; 3] [1; 2; 3] = true.
Proof.
  reflexivity.
Qed.

(*Given a list of constraints and an assignmet check if all of them are greater than zero*)
Fixpoint is_model {n_v : nat} {n_c : nat} :  (@constraints n_v n_c) -> (@assignment n_v) -> bool :=
  match n_c with
  | 0%nat => fun _ _ => true
  | S n_c' => fun cs model => ((is_model_c (hd cs) model) && (is_model (tl cs) model))%bool
  end.

(* Adds two vectors*)
Fixpoint vect_add {n : nat} (v1 v2 : t Z n) : t Z n :=
  match v1 in t _ n return t Z n -> t Z n with
  | [] => fun _  => []
  | x1:: v1' => fun v2 => (x1 + (hd v2)) :: (vect_add v1' (tl v2))
  end v2.

(*Multiply a vector by a scalar*)
Fixpoint vect_mul {n : nat} (a : nat) (v : t Z n) : t Z n :=
  match v with
  | [] => []
  | b :: v' => (Z.of_nat(a)*b) :: (vect_mul a v')
  end.

(*Given an list of scalars (d1...dn) and a list of costraints (c1..cn) it returns the linear combination (d1*c1 + ... + dn*cn) *)
Fixpoint comb_lin {n_v : nat} {n_c : nat} : (t nat n_c) -> (@constraints n_v n_c) -> t Z n_v :=
  match n_c with
  | 0%nat => fun _ _ => const 0 n_v
  | S n_c' =>  fun d cs => vect_add (vect_mul (hd d) (hd cs)) (comb_lin (tl d) (tl cs))
  end.

(*This function checks if a linear combination expressed by d over cs equals c*)
Definition farkas { n_v : nat } {n_c : nat }(d : t nat n_c) (cs : @constraints n_v n_c) (c : @constraint n_v) : bool :=
  eqb Z (fun x y => x =? y) (comb_lin d cs) c.

Example test_comb_lin :  comb_lin [1%nat;2%nat] [[3;4]%vector;[5;6]%vector]%list = [13; 16]%list.
Proof. reflexivity. Qed.

Example test_farkas : farkas [1%nat;1%nat] [[1;1]%vector;[1;1]%vector]%list [2; 2] = true.
Proof. reflexivity. Qed.

(* Definition of imp_checker and the snd that it works*)
Definition imp_checker {n_v : nat} {n_c : nat }: Type := @constraints n_v n_c -> @constraint n_v -> bool.

(* We force that the model ends in 1, that way the last element represent the constant*)
Fixpoint adapt {n : nat } : @assignment n -> @assignment (S n):=
  match n with
  | 0%nat => fun _ => [1]
  | S n' => fun model => (hd model) :: (adapt (tl model))
  end. 

Definition imp_checker_snd {n_v : nat} {n_c : nat } (chkr : @imp_checker (S n_v) n_c) : Prop :=
  forall cs c,
    chkr cs c = true ->
    forall (model : @assignment (n_v)), @is_model (S n_v) n_c cs (adapt model) = true -> @is_model_c (S n_v) c (adapt model) = true.

(*Lemmas for the soundness of the imp_checker*)

Lemma eq_snd : forall x y : Z, (x =? y) = true <-> x = y.
Proof.
  exact Z.eqb_eq.
Qed.

Lemma le_snd : forall x y : Z, (x >=? y) = true <-> x >= y.
Proof.
  repeat rewrite Z.ge_le_iff.
  exact Z.geb_ge.
Qed.

Lemma sum_gt_is_gt : forall (m n : Z), m >=? 0 = true -> n >=? 0 = true -> m + n >=? 0 = true.
Proof.
  intros m n.
  repeat rewrite le_snd.
  repeat rewrite Z.ge_le_iff. intros m_gt_z n_gt_z. rewrite Z.add_nonneg_nonneg.
  reflexivity. rewrite m_gt_z. reflexivity. rewrite n_gt_z. reflexivity.
Qed.

Lemma prod_gt_is_gt : forall (m n : Z), m >=? 0 = true -> n >=? 0 = true -> m * n >=? 0 = true.
Proof.
  intros m n.
  repeat rewrite le_snd.
  repeat rewrite Z.ge_le_iff. intros m_gt_z n_gt_z. rewrite Z.mul_nonneg_nonneg.
  reflexivity. rewrite m_gt_z. reflexivity. rewrite n_gt_z. reflexivity.
Qed.

Lemma vect_add_snd : forall {n_v : nat} (c1 c2 : @constraint n_v) (model : @assignment n_v),
   (eval c1 model) + (eval c2 model) = eval (vect_add c1 c2) model.
Proof.
  intros n_v c1 c2 model.
  induction c1 as [| a n_v' c1' IHc'].
  - (* n_v = 0*)
    reflexivity.
  - (*n_v = S n_v'*) 
    simpl. rewrite <- IHc'. ring.
Qed.
    
Lemma vect_add_gt_is_gt : forall {n_v : nat} (c1 c2 : @constraint n_v) (model : @assignment n_v),
 is_model_c c1 model = true -> is_model_c c2 model = true -> is_model_c (vect_add c1 c2) model = true.
Proof.
  intros n_v c1 c2 model.
  unfold is_model_c.
  intros c1_gt_z c2_gt_z.
  induction n_v as [| n_v' IHn_v'].
  - (* n_v = 0*)
    reflexivity.
  - (* n_v = S n_v' *) rewrite <- vect_add_snd.
    rewrite sum_gt_is_gt.
    reflexivity.
    rewrite c1_gt_z. reflexivity.
    rewrite c2_gt_z. reflexivity.
Qed.   

Lemma vect_mul_snd : forall {n_v : nat} (c : @constraint n_v) (model : @assignment n_v) (d : nat),
    (Z.of_nat(d) * eval c model = eval (vect_mul d c) model).
Proof.
  intros n_v c model d.
  induction c as [| a c' n_v' IHc'].
  - (*c = []*) 
    simpl. rewrite Z.mul_0_r.
    reflexivity.
  - (*c = a c' n_v*)
    simpl. rewrite Z.mul_add_distr_l. rewrite IHc'.
    ring.
Qed.

Lemma vect_mul_gt_is_gt : forall {n : nat} (d : nat) (c : @constraint n) (model : @assignment n),
    is_model_c c model = true -> is_model_c (vect_mul d c) model = true.
Proof.
  intros n d c model.
  unfold is_model_c. intros c_gt_z.
  simpl. rewrite <- vect_mul_snd.
  rewrite prod_gt_is_gt. reflexivity.
  rewrite le_snd.
  rewrite Z.ge_le_iff.
  rewrite Zle_0_nat. reflexivity.
  rewrite c_gt_z. 
  reflexivity.
Qed.
  
Lemma eval_0_gt_0 : forall (n : nat) (model :  @assignment n),
    eval (const 0 n) model >=? 0 = true.
Proof.
  intros n model.
  induction model as [| x1 n' model' IHmodel'].
  - (* model = [] *)
    reflexivity.
  - (* model = x1 :: model' *)  
    simpl.
    exact IHmodel'.
Qed.


Lemma comb_lin_is_gt : forall {n_v : nat} {n_c : nat} (cs : @constraints n_v n_c) (d : t nat n_c) (model : assignment),
    is_model cs model = true -> is_model_c (comb_lin d cs) model = true.
Proof.
  intros n_v n_c cs d model.
  induction n_c as [| n_c'].
  - (*n_c = 0*) simpl.
    unfold is_model_c.
    rewrite eval_0_gt_0.
    reflexivity.
  - (*n_c = S n_c'*)
    simpl.
    rewrite Bool.andb_true_iff.
    intro precond.
    rewrite vect_add_gt_is_gt.
    reflexivity.
    rewrite vect_mul_gt_is_gt.
    reflexivity.
    destruct precond.
    rewrite H.
    reflexivity.
    rewrite IHn_c'.
    reflexivity.
    destruct precond.
    rewrite H0.
    reflexivity.
Qed.


Theorem snd : forall (n_v n_c : nat) (d : t nat n_c) , @imp_checker_snd n_v n_c (farkas d).
Proof.
  intros n_v n_c d.
  unfold imp_checker_snd.
  unfold farkas.
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
    intro c_is_comb_lin.
    intro model.
    replace c with (comb_lin d cs).
    intro cs_is_model.
    rewrite comb_lin_is_gt.
    reflexivity.
    rewrite cs_is_model.
    reflexivity.
    apply Z.eqb_eq.
Qed.
