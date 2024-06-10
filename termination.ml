
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val tail_add : nat -> nat -> nat **)

  let rec tail_add n m =
    match n with
    | O -> m
    | S n0 -> tail_add n0 (S m)
 end

type 'a t =
| Nil0
| Cons0 of 'a * nat * 'a t

(** val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2 **)

let caseS h _ = function
| Nil0 -> Obj.magic __
| Cons0 (h0, n0, t0) -> h h0 n0 t0

(** val hd : nat -> 'a1 t -> 'a1 **)

let hd n =
  caseS (fun h _ _ -> h) n

(** val const : 'a1 -> nat -> 'a1 t **)

let rec const a = function
| O -> Nil0
| S n0 -> Cons0 (a, n0, (const a n0))

(** val tl : nat -> 'a1 t -> 'a1 t **)

let tl n =
  caseS (fun _ _ t0 -> t0) n

(** val shiftin : nat -> 'a1 -> 'a1 t -> 'a1 t **)

let rec shiftin _ a = function
| Nil0 -> Cons0 (a, O, Nil0)
| Cons0 (h, n0, t0) -> Cons0 (h, (S n0), (shiftin n0 a t0))

(** val append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t **)

let rec append _ p v w =
  match v with
  | Nil0 -> w
  | Cons0 (a, n0, v') -> Cons0 (a, (add n0 p), (append n0 p v' w))

(** val rev_append_tail : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t **)

let rec rev_append_tail _ p v w =
  match v with
  | Nil0 -> w
  | Cons0 (a, n0, v') -> rev_append_tail n0 (S p) v' (Cons0 (a, p, w))

(** val rev_append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t **)

let rev_append =
  rev_append_tail

(** val rev : nat -> 'a1 t -> 'a1 t **)

let rev n v =
  rev_append n O v Nil0

(** val map : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t **)

let rec map f _ = function
| Nil0 -> Nil0
| Cons0 (a, n0, v') -> Cons0 ((f a), n0, (map f n0 v'))

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p -> (match y with
               | XI q -> XI (add p q)
               | XO q -> XO (add p q)
               | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH -> (match y with
             | XI q -> XI (succ q)
             | XO q -> XO (succ q)
             | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' -> (match y with
                  | Zneg y' -> compOpp (Pos.compare x' y')
                  | _ -> Lt)

  (** val geb : z -> z -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> False
    | _ -> True

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)
 end

type constraint0 = z t

type constraints = constraint0 t

(** val vect_add : nat -> z t -> z t -> z t **)

let rec vect_add _ v1 v2 =
  match v1 with
  | Nil0 -> Nil0
  | Cons0 (x1, n0, v1') ->
    Cons0 ((Z.add x1 (hd n0 v2)), n0, (vect_add n0 v1' (tl n0 v2)))

(** val vect_mul : nat -> nat -> z t -> z t **)

let rec vect_mul _ a = function
| Nil0 -> Nil0
| Cons0 (b, n0, v') -> Cons0 ((Z.mul (Z.of_nat a) b), n0, (vect_mul n0 a v'))

(** val vect_mul_Z : nat -> z -> z t -> z t **)

let rec vect_mul_Z _ a = function
| Nil0 -> Nil0
| Cons0 (b, n0, v') -> Cons0 ((Z.mul a b), n0, (vect_mul_Z n0 a v'))

(** val comb_conic : nat -> nat -> nat t -> constraints -> z t **)

let rec comb_conic n_v n_c x x0 =
  match n_c with
  | O -> const Z0 n_v
  | S n_c' ->
    vect_add n_v (vect_mul n_v (hd n_c' x) (hd n_c' x0))
      (comb_conic n_v n_c' (tl n_c' x) (tl n_c' x0))

(** val is_gt_on_last : nat -> constraint0 -> constraint0 -> bool **)

let rec is_gt_on_last n_v x x0 =
  match n_v with
  | O -> True
  | S n_v' ->
    (match n_v' with
     | O -> Z.geb (hd n_v' x0) (hd n_v' x)
     | S _ ->
       (match Z.eqb (hd n_v' x) (hd n_v' x0) with
        | True -> is_gt_on_last n_v' (tl n_v' x) (tl n_v' x0)
        | False -> False))

(** val is_minus_one : nat -> constraint0 -> bool **)

let rec is_minus_one n_v c =
  match n_v with
  | O -> Z.eqb (hd O c) (Zneg XH)
  | S n_v' ->
    (match Z.eqb (hd (S n_v') c) Z0 with
     | True -> is_minus_one n_v' (tl (S n_v') c)
     | False -> False)

type lex_function = z t

(** val c_of_f : nat -> lex_function -> constraint0 **)

let c_of_f n_var f =
  let rev_f = rev (S n_var) f in
  let const_f = hd n_var rev_f in
  let coef = rev n_var (tl n_var rev_f) in
  shiftin (add n_var n_var) const_f (append n_var n_var coef (const Z0 n_var))

(** val c_of_f' : nat -> lex_function -> constraint0 **)

let c_of_f' n_var f =
  let rev_f = rev (S n_var) f in
  let const_f = hd n_var rev_f in
  let coef = rev n_var (tl n_var rev_f) in
  shiftin (add n_var n_var) (Z.opp const_f)
    (append n_var n_var (const Z0 n_var) (map Z.opp n_var coef))

(** val cs_f_i_minus_f_i' : nat -> lex_function -> constraint0 **)

let cs_f_i_minus_f_i' n_var f =
  vect_add (S (add n_var n_var)) (c_of_f n_var f) (c_of_f' n_var f)

(** val cs_f_i'_minus_f_i : nat -> lex_function -> constraint0 **)

let cs_f_i'_minus_f_i n_var f =
  vect_mul_Z (S (add n_var n_var)) (Zneg XH) (cs_f_i_minus_f_i' n_var f)

(** val new_cs : nat -> nat -> constraints -> lex_function -> constraints **)

let new_cs n_var n_c cs f =
  shiftin (S n_c) (cs_f_i_minus_f_i' n_var f)
    (shiftin n_c (cs_f_i'_minus_f_i n_var f) cs)

type list_d = nat list

(** val my_of_list : nat -> nat list -> nat t option **)

let rec my_of_list n = function
| Nil -> (match n with
          | O -> Some (const O O)
          | S _ -> None)
| Cons (x, xs) ->
  (match n with
   | O -> None
   | S n' ->
     (match my_of_list n' xs with
      | Some v -> Some (Cons0 (x, n', v))
      | None -> None))

(** val lex_func : nat -> nat -> constraints -> nat t -> constraint0 -> bool **)

let lex_func n_var n_c cs d f =
  is_gt_on_last (S n_var) (comb_conic (S n_var) n_c d cs) f

(** val is_lex :
    nat -> nat -> constraints -> lex_function list -> (list_d, list_d) prod list -> bool **)

let rec is_lex n_var n_c cs list_f list_of_d =
  match list_f with
  | Nil ->
    (match list_of_d with
     | Nil -> False
     | Cons (d, _) ->
       let d_i = fst d in
       let vec_d = my_of_list n_c d_i in
       (match vec_d with
        | Some v ->
          is_minus_one (add n_var n_var) (comb_conic (S (add n_var n_var)) n_c v cs)
        | None -> False))
  | Cons (f, fs) ->
    let f_i = c_of_f n_var f in
    let f_i_minus_f_i' = cs_f_i_minus_f_i' n_var f in
    (match list_of_d with
     | Nil -> False
     | Cons (d, ds) ->
       let d_i_1 = fst d in
       let d_i_2 = snd d in
       let vec_d_1 = my_of_list n_c d_i_1 in
       let vec_d_2 = my_of_list n_c d_i_2 in
       (match vec_d_1 with
        | Some v1 ->
          (match vec_d_2 with
           | Some v2 ->
             (match match lex_func (add n_var n_var) n_c cs v1 f_i with
                    | True -> lex_func (add n_var n_var) n_c cs v2 f_i_minus_f_i'
                    | False -> False with
              | True -> is_lex n_var (S (S n_c)) (new_cs n_var n_c cs f) fs ds
              | False -> False)
           | None -> False)
        | None -> False))
