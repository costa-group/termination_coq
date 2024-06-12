Require Import Vectors.Vector.
Require Import ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Lia.

Import VectorNotations.

Local Open Scope Z_scope.
Local Open Scope vector_scope.

(*Definitions*)

Definition constraint {n_v : nat} : Type := t Z n_v.

Definition constraints {n_v : nat} {n_c : nat } : Type := t (@constraint n_v) n_c.

(*When defining a model we should allways add a 1 at the end*)
Definition assignment { n : nat} : Type := t Z n.


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

Fixpoint vect_mul_Z {n : nat} (a : Z) (v : t Z n) : t Z n :=
  match v with
  | [] => []
  | b :: v' => (a*b) :: (vect_mul_Z a v')
  end.

(*Given an list of scalars (d1...dn) and a list of costraints (c1..cn) it returns the linear combination (d1*c1 + ... + dn*cn) *)
Fixpoint comb_conic {n_v : nat} {n_c : nat} : (t nat n_c) -> (@constraints n_v n_c) -> t Z n_v :=
  match n_c with
  | 0%nat => fun _ _ => const 0 n_v
  | S n_c' =>  fun d cs => vect_add (vect_mul (hd d) (hd cs)) (comb_conic (tl d) (tl cs))
  end.

Example test_comb_conic :  comb_conic [1%nat;2%nat] [[3;4]%vector;[5;6]%vector]%list = [13; 16]%list.
Proof. reflexivity. Qed.

(* We force that the model ends in 1, that way the last element represent the constant*)
Fixpoint adapt {n : nat } : @assignment n -> @assignment (S n):=
  match n with
  | 0%nat => fun _ => [1]
  | S n' => fun model => (hd model) :: (adapt (tl model))
  end.

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

(*Propiedades sobre la suma y el producto con escalares de vectores*)

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
  
Lemma vect_add_lt_is_lt : forall {n_v : nat} (c1 c2 : @constraint n_v) (model : @assignment n_v),
    eval (vect_add c1 c2) model < 0 ->
    eval c1 model < 0 \/ eval c2 model < 0.
Proof.
  intros n_v c1 c2 model.
  induction n_v as [| n_v' IHn_v'].
  - (* n_v = 0 *)
    simpl. lia.
  - (* n_v = S n_v' *)
    rewrite <- vect_add_snd.
    Search Z.add ?p ?g Z.lt 0.
    apply Z.add_neg_cases.
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

Lemma vect_mul_lt_is_lt : forall {n_v : nat} (d : nat ) (c : @constraint n_v) (model : @assignment n_v),
    eval (vect_mul d c) model < 0 -> eval c model < 0.
Proof.
  intros n d c model.
  rewrite <- vect_mul_snd.
  lia.
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


Lemma comb_conic_is_gt : forall {n_v : nat} {n_c : nat} (cs : @constraints n_v n_c) (d : t nat n_c) (model : assignment),
    is_model cs model = true -> is_model_c (comb_conic d cs) model = true.
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


(*This function checks if a conic combination expressed by d over cs equals c*)
Definition is_equal { n_v : nat } {n_c : nat }(d : t nat n_c) (cs : @constraints n_v n_c) (c : @constraint n_v) : bool :=
  eqb Z (fun x y => x =? y) (comb_conic d cs) c.

Example test_is_equal : is_equal [1%nat;1%nat] [[1;1]%vector;[1;1]%vector]%list [2; 2] = true.
Proof. reflexivity. Qed.

Fixpoint is_gt_on_last {n_v : nat } : @constraint n_v -> @constraint n_v -> bool :=
  match n_v with
  | 0%nat => fun _ _ => true
  | S n_v' => match n_v' with
              | 0%nat => fun c c' => hd c' >=? hd c
              | n => fun c c' => ((hd c =? hd c') && (@is_gt_on_last n (tl c) (tl c')))%bool
              end                                                                     
  end.

Example test_is_gt_on_last_1 : is_gt_on_last [1;2;3] [1;2;4] = true.
Proof. reflexivity. Qed.                                                                 

Example test_is_gt_on_last_2 : is_gt_on_last [1;2;3] [1;2;2] = false.
Proof. reflexivity. Qed.

Example test_is_gt_on_last_3 : is_gt_on_last [1;3;3] [1;2;3] = false.
Proof. reflexivity. Qed.

Lemma eval_is_gt : forall {n_v :nat} (c c' : @constraint ( S n_v)) (model : assignment),
    @is_gt_on_last (S n_v) c c' = true -> (*is_model_c c model = true ->*)
    @eval (S n_v) c' (adapt model) >= @eval (S n_v) c (adapt model).
Proof.
  intro n_v.
  induction n_v as [| n_v' IHn_v'].
  - (*n_v = 0 -> S n_v = 1 *)
    (*Caso en que solo tenemos la constante*)
    intros c c' model.
    intro is_gt_on_last_true.
    simpl. simpl in is_gt_on_last_true. rewrite le_snd in is_gt_on_last_true.
    lia.
  - (*n_v = S n_v' -> S n_v = S S n_v'*)
    (*Caso en que tenemos algo más que la constante*)
    intros c c' model.
    intro is_gt_on_last_true. simpl in is_gt_on_last_true.
    destruct n_v'.
    --(*n_v' = 0*)
      rewrite Bool.andb_true_iff in is_gt_on_last_true. destruct is_gt_on_last_true.
      rewrite eq_snd in H. rewrite le_snd in H0.
      simpl. repeat rewrite Z.add_0_r. repeat rewrite <- Zred_factor0.
      lia.
    --(*n_v' = S n_''*)
      rewrite Bool.andb_true_iff in is_gt_on_last_true. destruct is_gt_on_last_true.
      rewrite eq_snd in H. unfold is_model_c.
      apply (@IHn_v' (tl c) (tl c') (tl model)) in H0.
      simpl. rewrite H. simpl in H0. lia.      
Qed.

Fixpoint is_minus {n_v : nat} : @constraint (S n_v) -> bool :=
  match n_v with
  | 0%nat => fun c => hd c <? 0
  | S n_v' => fun c => ((hd c =? 0) && (is_minus (tl c)))%bool
  end.

Example test_is_minus_one_1 : is_minus [1;2;3] = false.
Proof. reflexivity. Qed.

Example test_is_minus_one_2 : is_minus [0;0;-1] = true.
Proof. reflexivity. Qed.

Lemma eval_minus_one {n_v : nat} (c : @constraint (S n_v)) :
  forall (model : @assignment n_v),
    is_minus c = true ->
    eval c (adapt model) < 0.
Proof.
  intros model.
  induction n_v as [| n_v' IHn_v'].
  - (* n_v = 0*)
    simpl. rewrite Z.ltb_lt.  
    rewrite Z.add_0_r. repeat rewrite <- Zred_factor0.
    lia.
  - (* n_v = (S n_v')*)  
    simpl. rewrite Bool.andb_true_iff. intro h. destruct h.
    rewrite eq_snd in H. rewrite H. apply (@IHn_v' (tl c) (tl model)) in H0.
    simpl in H0. rewrite Z.mul_0_l. rewrite Z.add_0_l. exact H0.
Qed.


Lemma eval_const_0_is_0 {n_v : nat} :
  forall model : assignment,
    eval (const 0 n_v) model = 0.
Proof.
  intros model.
  induction n_v as [| n_v' IHn_v'].
  - (*n_v = 0*)
    simpl. reflexivity.
  - (*n_v = S (n_v') *)
    simpl. rewrite IHn_v'. reflexivity.
Qed.

Fixpoint same_vector {n_v : nat} : @constraint n_v -> @constraint n_v -> bool :=
  match n_v with
  | 0%nat => fun _ _ => true
  | S n_v' => fun c1 c2 => ((hd c1 =? hd c2) && (same_vector (tl c1) (tl c2)))%bool
  end.

Lemma same_vector_refl {n_v : nat} :
    forall c : @constraint n_v, same_vector c c = true.
Proof.
  intro c.
  induction n_v as [| n_v' IHn_v'].
  simpl. reflexivity.
  simpl. rewrite Bool.andb_true_iff. split.
  rewrite eq_snd. reflexivity. rewrite IHn_v'. reflexivity.
Qed.

Lemma same_vector_snd {n_v : nat } :
  forall (c1 c2 : @constraint n_v), same_vector c1 c2 = true -> c1 = c2.
Proof.
  intros c1 c2.
  induction n_v as [| n_v' IHn_v'].
  - intros same. rewrite nil_spec. rewrite (@nil_spec Z c1). reflexivity.
  - simpl. intros h. rewrite Bool.andb_true_iff in h. destruct h.
    apply IHn_v' in H0. rewrite eq_snd in H. rewrite eta. rewrite (@eta Z n_v' c1).
    rewrite H. rewrite H0. reflexivity.
Qed.
    
Fixpoint is_in_the_vector {n_c n_v : nat} : @constraint n_v -> @constraints n_v n_c -> bool :=
  match n_c with
  | 0%nat => fun _ _ => false
  | S n_c' => fun c cs => (same_vector c (hd cs) || is_in_the_vector c (tl cs))%bool
  end.

Lemma is_minus_one_implies {n_v n_c : nat} (d : t nat n_c) (cs : @constraints n_v n_c) :
  forall (model : @assignment n_v),
    eval (comb_conic d cs)  model < 0 ->
    exists (c : @constraint n_v), (is_in_the_vector c cs = true) /\ (eval c model) < 0.
Proof.    
  intros model.
  induction n_c as [| n_c' IHn_c'].
  - (* n_c = 0 *)
    simpl. rewrite eval_const_0_is_0. lia.
  - (* n_c = S n_c' *)
    simpl. intro h.
    Check vect_add_lt_is_lt.
    apply vect_add_lt_is_lt in h. destruct h.
    apply vect_mul_lt_is_lt in H.
    exists (hd cs). split. rewrite Bool.orb_true_iff.
    left. simpl. rewrite same_vector_refl. reflexivity.
    exact H.
    apply IHn_c' in H. destruct H as [c H].
    exists c. split. rewrite Bool .orb_true_iff. right.
    destruct H. exact H.
    destruct H. exact H0.
Qed.

Lemma if_constraint_lt_0_model_false {n_v n_c : nat} (cs : @constraints (S n_v) n_c) :
  forall (model : @assignment n_v),
    (exists c : @constraint (S n_v), (is_in_the_vector c cs = true) /\ (eval c (adapt model) < 0)) ->
    is_model cs (adapt model) = false.
Proof.    
  intros model.
  induction n_c as [| n_c' IHn_c'].
  - simpl. intro h. destruct h. lia.
  - intro h. simpl in h. destruct h as [c Hc]. destruct Hc. 
    simpl. rewrite Bool.orb_true_iff in H. destruct H.
    rewrite Bool.andb_true_iff in H. destruct H. 

    rewrite Bool.andb_false_iff.
    left.
    unfold is_model_c. simpl. rewrite Z.geb_leb. rewrite Z.leb_gt.
    replace (hd cs) with c.
    exact H0. rewrite eq_snd in H. rewrite  (@eta Z n_v c). rewrite (@eta Z n_v (hd cs)).
    rewrite H. apply same_vector_snd in H1. rewrite H1. reflexivity.

    rewrite Bool.andb_false_iff. right. apply IHn_c'. exists c.
    split. exact H.
    simpl. exact H0.
Qed.
