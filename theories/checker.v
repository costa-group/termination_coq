Require Import Vectors.Vector.
Require Import ZArith.
Require Import Lia.
Local Open Scope Z_scope.

(*We import the definions and functions we defined for the constraints*)
Require Import constraint.

Import VectorNotations.
Local Open Scope vector_scope.

(* Definition of imp_checker and the snd that it works*)
Definition imp_checker {n_v : nat} {n_c : nat }: Type := @constraints n_v n_c -> @constraint n_v -> bool.

(* Returns true if the cs implies the c *)
Definition cs_imp_c {n_v n_c : nat} (cs : constraints) (c : constraint) : Prop :=
  forall (model : @assignment (n_v)),
    @is_model (S n_v) n_c cs (adapt model) = true -> @is_model_c (S n_v) c (adapt model) = true.

(*Returns true if the cs implie the cs' *)
Fixpoint cs_imp_cs' {n_v n_c n_c' : nat} : (@constraints (S n_v) n_c) -> (@constraints (S n_v) n_c') -> Prop :=
  match n_c' with
  | 0%nat => fun _ _ => True
  | S n_c'' => fun cs cs' => cs_imp_c cs (hd cs') /\ cs_imp_cs' cs (tl cs')
  end.

Definition imp_checker_snd {n_v : nat} {n_c : nat } (chkr : @imp_checker (S n_v) n_c) : Prop :=
  forall (cs : constraints) (c : constraint),
    chkr cs c = true ->
     cs_imp_c cs c.

(*Ensures that if c_comb is comb_conic of cs and d then cs implies c_comb *)
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
    -> is_ge_on_last c c' = true                                   
    -> is_model_c c' (adapt model) = true.
Proof.
  intros n_v c c' model.
  unfold is_model_c.
  intro is_model_c. rewrite le_snd in is_model_c.
  intro is_ge_on_last_true.
  apply (@eval_is_gt (n_v) c c' (model)) in is_ge_on_last_true.
  rewrite le_snd.
  apply (@Zge_trans (eval c' (adapt model)) (eval c (adapt model)) 0).
  exact is_ge_on_last_true.
  exact is_model_c.
Qed.

(* Farka's Lemma*)
Theorem farkas : forall {n_v n_c : nat},
  forall (cs : constraints) (d : t nat n_c) (c_comb : @constraint (S n_v)),
    is_equal d cs c_comb = true ->
    forall (model : @assignment n_v) (c : @constraint (S n_v)), 
    is_model cs (adapt model) = true ->
    is_ge_on_last c_comb c = true ->
    is_model_c c (adapt model) = true.
Proof.
  intros n_v n_c cs d c_comb.
  intros h0 model c h1 h2.
  apply (@comb_conic_is_model n_v n_c cs c_comb d model) in h0.
  apply (@farkas_gt n_v c_comb c model) in h0.
  assumption. assumption. assumption.
Qed.

(* What it means to be unsatisfatiable*)
Definition unsat {n_v n_c : nat} (cs : @constraints (S n_v) n_c) :=
  forall (model : @assignment n_v),
    is_model cs (adapt model) = false.

(* Sufficient condition for being unsat*)
Lemma unsat_suf : forall {n_v n_c : nat} (cs : @constraints (S n_v) n_c) (d : t nat n_c),
    is_minus (comb_conic d cs) = true ->
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

(* Auxiliar function that truncates last element of vector*)
Fixpoint without_last {n_var : nat} : (t Z (S n_var)) -> t Z n_var :=
  match n_var with
  | 0%nat => fun _ => []
  | S n => fun f => (hd f)::(without_last (tl f))
  end.

(*This function receives a lex function and returns the corresponding constraint*)
Definition c_of_f {n_var : nat} (f : @lex_function n_var) :  @constraint (S (n_var + n_var)) :=
  let const_f := (Vector.last f) in
  let coef := without_last f in
  shiftin const_f (coef ++ (const 0 n_var)).

Example test_c_of_f : c_of_f [1;0]%vector = [1;0;0].
Proof. reflexivity. Qed.

(*This function receives a lex function and returns the corresponding constraint with the signus changed*)
Definition c_of_f' {n_var : nat} (f : @lex_function n_var) :  @constraint (S (n_var + n_var)) :=
  let const_f := Vector.last f in
  let coef := without_last f in
  shiftin (-const_f) ((const 0 n_var) ++ (map (fun x => -x) coef)).

Example test_c_of_f' : c_of_f' [1; 0]%vector = [0;-1;0].
Proof. reflexivity. Qed.

(* This function returns the constaint that represent the condition f1(x) - f1(x') >= 0 *)
Definition cs_f_i_minus_f_i' {n_var : nat} (f : @lex_function n_var) : @constraint (S (n_var + n_var)) :=
  vect_add (c_of_f f)  (c_of_f' f).

Definition cs_f_i'_minus_f_i {n_var : nat} (f : @lex_function n_var) : @constraint (S (n_var + n_var)) :=
  vect_mul_Z (-1) (cs_f_i_minus_f_i' f).

Definition cs_of_two {n_var : nat} (c c' : @constraint n_var) : constraints :=
  shiftin c' (shiftin c []).

(* This function receives a set of constraints(cs) and a ranking function(f)
   and returns its composition in a set of constraints *)
Definition new_cs {n_var n_c : nat} (cs : @constraints (S (n_var + n_var)) n_c)  (f : @lex_function n_var) : constraints :=
 shiftin (cs_f_i_minus_f_i' f) (shiftin (cs_f_i'_minus_f_i f) cs).

Definition cs_f_i_minus_f_i'_is_zero {n_var : nat} (f : @lex_function n_var) :  constraints :=
  cs_of_two (cs_f_i_minus_f_i' f) (cs_f_i'_minus_f_i f).

(*Representations of the Ds*)
Definition list_d := list nat.

Require Import List.

Import ListNotations.

(*Defined to ensure Coq that the lists we are working are the rigth length*)
Fixpoint my_of_list (n : nat) (l: list nat) : option (t nat n) :=
  match l with
  | []%list =>
      match n with
      | O => Some (const 0%nat 0)
      | _ => None
      end
  | (x::xs)%list =>
      match n with
      | O => None
      | S n' => match my_of_list n' xs with
                | None => None
                | Some v => Some (x::v)%vector
                end
      end
  end.

(*Function that checks if the d's provided suit the set of constraints(cs) and the ranking function(f)*)
Definition lex_func {n_var n_c} (cs : @constraints (S n_var) n_c) (d : t nat n_c) (f : @constraint (S n_var)) : bool :=
  is_ge_on_last (comb_conic d cs) f.

(*Functions that checks if the loop represented by the set of constraints(cs) ends given a list of
  ranking functions(f) and the d's*)
Fixpoint is_lex {n_var n_c : nat} (cs : @constraints (S (n_var + n_var)) n_c) (list_f : list (@lex_function n_var)) (list_of_d : list ((list_d)*(list_d))) : bool :=
  match list_f with
  | [] => match list_of_d with
          | [] => false
          | d::ds => let d_i := fst d in
                     let vec_d := my_of_list n_c d_i in
                     match vec_d with
                     | None => false
                     | Some v => is_minus (comb_conic v cs)
                     end
          end
  | f::fs =>let f_i := c_of_f f in
            let f_i_minus_f_i' := cs_f_i_minus_f_i' f in
            match list_of_d with
            | [] => false
            | d::ds =>
                let d_i_1 := fst d in
                let d_i_2 := snd d in
                let vec_d_1 := my_of_list n_c d_i_1 in
                let vec_d_2 := my_of_list n_c d_i_2 in
                match vec_d_1 with
                | None => false
                | Some v1 => match vec_d_2 with
                             | None => false
                             | Some v2 => ((lex_func cs v1 f_i) &&
                                             (lex_func cs v2 f_i_minus_f_i') &&
                                             (is_lex (new_cs cs f) fs ds)
                                          )%bool
                             end
                end
            end
  end.

(*Inductive proposition on the lex functions*)
Inductive Lex {n_var n_c : nat} : (@constraints (S (n_var + n_var)) n_c) -> list (@lex_function n_var) -> Prop :=
| basic
    (cs : (@constraints (S (n_var + n_var)) n_c))
    (list_f : list (@lex_function n_var))
    (H1 : unsat cs)
  : (Lex cs list_f)    
| other
    (cs : (@constraints (S (n_var + n_var)) n_c))
    (list_f : list (@lex_function n_var))
    (f : @lex_function n_var)
    (fs : list (@lex_function n_var))
    (H' : list_f = f::fs)
    (H1 : cs_imp_c cs (cs_f_i_minus_f_i' f))
    (H2 : cs_imp_c cs (c_of_f f))
    (H3 : Lex  (new_cs cs f) fs)
  : (Lex cs list_f).

(*Some auxiliar lemmas*)
Lemma aux_eq_comb_conic :
  forall {n_var n_c : nat}
         (cs : @constraints (S n_var) n_c)
         (d : t nat n_c),
    is_equal d cs (comb_conic d cs) = true.
Proof.
  intros n_var n_c cs d.
  unfold is_equal.
  rewrite eqb_eq.
  reflexivity.
  exact Z.eqb_eq.
Qed. 
  
Lemma is_equal_imp :
  forall {n_var n_c : nat}
         (cs : @constraints (S n_var) n_c)
         (f : @constraint (S n_var))
         (d : t nat n_c),
    lex_func cs d f = true -> cs_imp_c cs f.
Proof.
  intros n_var n_c cs f d.
  intro H.
  unfold lex_func in H.  
  unfold cs_imp_c.
  intros model H1.
  apply (@farkas n_var n_c cs d (comb_conic d cs) (@aux_eq_comb_conic n_var n_c cs d) model f) in H1.
  exact H1.
  exact H.
Qed.

(*Theorem that ensures that when the function is_lex says true is sufficient for proving Lex *) 
Theorem is_lex_imp_Lex :
  forall {n_var : nat}
         (list_f : list (@lex_function n_var))
         {n_c : nat}
         (cs : @constraints (S (n_var + n_var)) n_c)
         (list_of_d : list ((list_d)*(list_d))),
    is_lex cs list_f list_of_d = true -> Lex cs list_f.
Proof.
  intros n_var list_f.
  induction list_f as [| f1 fs IHf'].
  - simpl. intros n_c cs list_of_d.
    induction list_of_d as [| d1 ds IHd'].
    -- intro H. apply Bool.diff_false_true in H.
       contradiction.
    -- destruct (my_of_list n_c (fst d1)).
       --- intro H. apply unsat_suf in H. exact (basic cs [] H).
       --- intro H. apply Bool.diff_false_true in H.
           contradiction.
  - simpl. intros n_c cs list_of_d H.
    induction list_of_d as [| d1 ds IHd'].
    --  apply Bool.diff_false_true in H.
       contradiction.
    -- destruct (my_of_list n_c (fst d1)).
       destruct (my_of_list n_c (snd d1)).
       --- apply andb_prop in H. destruct H. apply andb_prop in H. destruct H.
           apply is_equal_imp in H. apply is_equal_imp in H1.
           apply (@other n_var n_c cs (f1::fs) f1 fs (eq_refl) H1 H).
           apply (@IHf' (S (S (n_c))) (new_cs cs f1) ds H0).
       --- apply Bool.diff_false_true in H.
           contradiction.
       --- apply Bool.diff_false_true in H.
           contradiction.
Qed.         

