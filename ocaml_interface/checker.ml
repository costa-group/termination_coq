
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| x , _ -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| _ , y -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _::l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a::l1 -> a::(app l1 m)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n0 m =
  match n0 with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val even : nat -> bool **)

  let rec even = function
  | O -> true
  | S n1 -> (match n1 with
             | O -> false
             | S n' -> even n')
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

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
    | XO p ->
      (match y with
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
    | XH ->
      (match y with
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
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Pos.mul p q))

  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> true
             | Npos _ -> false)
    | Npos p -> (match m with
                 | N0 -> false
                 | Npos q -> Pos.eqb p q)

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x::l' -> app (rev l') (x::[])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a::t0 -> (f a)::(map f t0)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b::t0 -> f b (fold_right f a0 t0)

(** val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec combine l l' =
  match l with
  | [] -> []
  | x::tl0 -> (match l' with
               | [] -> []
               | y::tl' -> (x , y)::(combine tl0 tl'))

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
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val geb : z -> z -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> false
    | _ -> true

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)
 end

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| [] -> N0
| b::l' ->
  N.add (if b then Npos XH else N0) (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : char -> n **)

let n_of_ascii a =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun a0 a1 a2 a3 a4 a5 a6 a7 ->
    n_of_digits (a0::(a1::(a2::(a3::(a4::(a5::(a6::(a7::[])))))))))
    a

(** val nat_of_ascii : char -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

(** val eqb0 : char list -> char list -> bool **)

let rec eqb0 s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb0 s1' s2' else false)

(** val length0 : char list -> nat **)

let rec length0 = function
| [] -> O
| _::s' -> S (length0 s')

(** val substring : nat -> nat -> char list -> char list **)

let rec substring n0 m s =
  match n0 with
  | O ->
    (match m with
     | O -> []
     | S m' -> (match s with
                | [] -> s
                | c::s' -> c::(substring O m' s')))
  | S n' -> (match s with
             | [] -> s
             | _::s' -> substring n' m s')

type 'a t =
| Nil
| Cons of 'a * nat * 'a t

(** val rectS :
    ('a1 -> 'a2) -> ('a1 -> nat -> 'a1 t -> 'a2 -> 'a2) -> nat -> 'a1 t -> 'a2 **)

let rec rectS bas rect _ = function
| Nil -> Obj.magic __
| Cons (a, n0, v0) ->
  (match n0 with
   | O ->
     (match v0 with
      | Nil -> bas a
      | Cons (x, x0, x1) -> Obj.magic __ x x0 x1)
   | S nn' -> rect a nn' v0 (rectS bas rect nn' v0))

(** val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2 **)

let caseS h _ = function
| Nil -> Obj.magic __
| Cons (h0, n0, t0) -> h h0 n0 t0

(** val hd : nat -> 'a1 t -> 'a1 **)

let hd n0 =
  caseS (fun h _ _ -> h) n0

(** val last : nat -> 'a1 t -> 'a1 **)

let last n0 =
  rectS (fun a -> a) (fun _ _ _ h -> h) n0

(** val const : 'a1 -> nat -> 'a1 t **)

let rec const a = function
| O -> Nil
| S n1 -> Cons (a, n1, (const a n1))

(** val tl : nat -> 'a1 t -> 'a1 t **)

let tl n0 =
  caseS (fun _ _ t0 -> t0) n0

(** val shiftin : nat -> 'a1 -> 'a1 t -> 'a1 t **)

let rec shiftin _ a = function
| Nil -> Cons (a, O, Nil)
| Cons (h, n0, t0) -> Cons (h, (S n0), (shiftin n0 a t0))

(** val append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t **)

let rec append _ p v w =
  match v with
  | Nil -> w
  | Cons (a, n0, v') -> Cons (a, (add n0 p), (append n0 p v' w))

(** val map0 : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t **)

let rec map0 f _ = function
| Nil -> Nil
| Cons (a, n0, v') -> Cons ((f a), n0, (map0 f n0 v'))

type constraint0 = z t

type constraints = constraint0 t

(** val vect_add : nat -> z t -> z t -> z t **)

let rec vect_add _ v1 v2 =
  match v1 with
  | Nil -> Nil
  | Cons (x1, n0, v1') ->
    Cons ((Z.add x1 (hd n0 v2)), n0, (vect_add n0 v1' (tl n0 v2)))

(** val vect_mul : nat -> nat -> z t -> z t **)

let rec vect_mul _ a = function
| Nil -> Nil
| Cons (b, n0, v') -> Cons ((Z.mul (Z.of_nat a) b), n0, (vect_mul n0 a v'))

(** val vect_mul_Z : nat -> z -> z t -> z t **)

let rec vect_mul_Z _ a = function
| Nil -> Nil
| Cons (b, n0, v') -> Cons ((Z.mul a b), n0, (vect_mul_Z n0 a v'))

(** val comb_conic : nat -> nat -> nat t -> constraints -> z t **)

let rec comb_conic n_v n_c x x0 =
  match n_c with
  | O -> const Z0 n_v
  | S n_c' ->
    vect_add n_v (vect_mul n_v (hd n_c' x) (hd n_c' x0))
      (comb_conic n_v n_c' (tl n_c' x) (tl n_c' x0))

(** val is_ge_on_last : nat -> constraint0 -> constraint0 -> bool **)

let rec is_ge_on_last n_v x x0 =
  match n_v with
  | O -> true
  | S n_v' ->
    (match n_v' with
     | O -> Z.geb (hd n_v' x0) (hd n_v' x)
     | S _ ->
       (&&) (Z.eqb (hd n_v' x) (hd n_v' x0))
         (is_ge_on_last n_v' (tl n_v' x) (tl n_v' x0)))

(** val is_minus : nat -> constraint0 -> bool **)

let rec is_minus n_v c =
  match n_v with
  | O -> Z.ltb (hd O c) Z0
  | S n_v' -> (&&) (Z.eqb (hd (S n_v') c) Z0) (is_minus n_v' (tl (S n_v') c))

type lex_function = z t

(** val without_last : nat -> z t -> z t **)

let rec without_last n_var x =
  match n_var with
  | O -> Nil
  | S n0 -> Cons ((hd (S n0) x), n0, (without_last n0 (tl (S n0) x)))

(** val c_of_f : nat -> lex_function -> constraint0 **)

let c_of_f n_var f =
  let const_f = last n_var f in
  let coef = without_last n_var f in
  shiftin (add n_var n_var) const_f (append n_var n_var coef (const Z0 n_var))

(** val c_of_f' : nat -> lex_function -> constraint0 **)

let c_of_f' n_var f =
  let const_f = last n_var f in
  let coef = without_last n_var f in
  shiftin (add n_var n_var) (Z.opp const_f)
    (append n_var n_var (const Z0 n_var) (map0 Z.opp n_var coef))

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

let rec my_of_list n0 = function
| [] -> (match n0 with
         | O -> Some (const O O)
         | S _ -> None)
| x::xs ->
  (match n0 with
   | O -> None
   | S n' ->
     (match my_of_list n' xs with
      | Some v -> Some (Cons (x, n', v))
      | None -> None))

(** val lex_func :
    nat -> nat -> constraints -> nat t -> constraint0 -> bool **)

let lex_func n_var n_c cs d f =
  is_ge_on_last (S n_var) (comb_conic (S n_var) n_c d cs) f

(** val is_lex :
    nat -> nat -> constraints -> lex_function list -> (list_d * list_d) list
    -> bool **)

let rec is_lex n_var n_c cs list_f list_of_d =
  match list_f with
  | [] ->
    (match list_of_d with
     | [] -> false
     | d::_ ->
       let d_i = fst d in
       let vec_d = my_of_list n_c d_i in
       (match vec_d with
        | Some v ->
          is_minus (add n_var n_var)
            (comb_conic (S (add n_var n_var)) n_c v cs)
        | None -> false))
  | f::fs ->
    let f_i = c_of_f n_var f in
    let f_i_minus_f_i' = cs_f_i_minus_f_i' n_var f in
    (match list_of_d with
     | [] -> false
     | d::ds ->
       let d_i_1 = fst d in
       let d_i_2 = snd d in
       let vec_d_1 = my_of_list n_c d_i_1 in
       let vec_d_2 = my_of_list n_c d_i_2 in
       (match vec_d_1 with
        | Some v1 ->
          (match vec_d_2 with
           | Some v2 ->
             (&&)
               ((&&) (lex_func (add n_var n_var) n_c cs v1 f_i)
                 (lex_func (add n_var n_var) n_c cs v2 f_i_minus_f_i'))
               (is_lex n_var (S (S n_c)) (new_cs n_var n_c cs f) fs ds)
           | None -> false)
        | None -> false))

module Parser =
 struct
  (** val isWhite : char -> bool **)

  let isWhite c =
    let n0 = n_of_ascii c in
    (||)
      ((||) (N.eqb n0 (Npos (XO (XO (XO (XO (XO XH)))))))
        (N.eqb n0 (Npos (XI (XO (XO XH))))))
      ((||) (N.eqb n0 (Npos (XO (XI (XO XH)))))
        (N.eqb n0 (Npos (XI (XO (XI XH))))))

  type chartype =
  | Coq_white
  | Coq_other

  (** val chartype_rect : 'a1 -> 'a1 -> chartype -> 'a1 **)

  let chartype_rect f f0 = function
  | Coq_white -> f
  | Coq_other -> f0

  (** val chartype_rec : 'a1 -> 'a1 -> chartype -> 'a1 **)

  let chartype_rec f f0 = function
  | Coq_white -> f
  | Coq_other -> f0

  (** val classifyChar : char -> chartype **)

  let classifyChar c =
    if isWhite c then Coq_white else Coq_other

  (** val list_of_string : char list -> char list **)

  let rec list_of_string = function
  | [] -> []
  | c::s0 -> c::(list_of_string s0)

  (** val string_of_list : char list -> char list **)

  let string_of_list xs =
    fold_right (fun x x0 -> x::x0) [] xs

  type token = char list

  (** val tokenize_helper :
      chartype -> char list -> char list -> char list list **)

  let rec tokenize_helper cls acc xs =
    let tk = match acc with
             | [] -> []
             | _::_ -> (rev acc)::[] in
    (match xs with
     | [] -> tk
     | x::xs' ->
       (match cls with
        | Coq_white ->
          (match classifyChar x with
           | Coq_white -> app tk (tokenize_helper Coq_white [] xs')
           | Coq_other -> app tk (tokenize_helper Coq_other (x::[]) xs'))
        | Coq_other ->
          (match classifyChar x with
           | Coq_white -> app tk (tokenize_helper Coq_white [] xs')
           | Coq_other -> tokenize_helper Coq_other (x::acc) xs')))

  (** val tokenize : char list -> char list list **)

  let tokenize s =
    map string_of_list (tokenize_helper Coq_white [] (list_of_string s))

  (** val parseDecNumber' : char list -> nat -> nat option **)

  let rec parseDecNumber' x acc =
    match x with
    | [] -> Some acc
    | d::ds ->
      let n0 = nat_of_ascii d in
      if (&&)
           (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))) n0)
           (Nat.leb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      then parseDecNumber' ds
             (add (mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
               (sub n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S
                 O))))))))))))))))))))))))))))))))))))))))))))))))))
      else None

  (** val parseDecNumber : char list -> nat option **)

  let parseDecNumber x =
    parseDecNumber' (list_of_string x) O

  (** val parseNatList : char list list -> nat list **)

  let rec parseNatList = function
  | [] -> []
  | x_0::xs ->
    let num = parseDecNumber x_0 in
    (match num with
     | Some z_0 -> z_0::(parseNatList xs)
     | None -> [])

  (** val parseZList : char list list -> z list **)

  let rec parseZList = function
  | [] -> []
  | x_0::xs ->
    if eqb0 (substring O (S O) x_0) ('-'::[])
    then let n_x_0 = substring (S O) (sub (length0 x_0) (S O)) x_0 in
         let num = parseDecNumber n_x_0 in
         (match num with
          | Some z_0 -> (Z.opp (Z.of_nat z_0))::(parseZList xs)
          | None -> [])
    else let num = parseDecNumber x_0 in
         (match num with
          | Some z_0 -> (Z.of_nat z_0)::(parseZList xs)
          | None -> [])

  (** val get_num_var : char list list -> nat option **)

  let get_num_var x =
    match parseNatList x with
    | [] -> None
    | x_0::l -> (match l with
                 | [] -> Some x_0
                 | _::_ -> None)

  (** val get_num_const : char list list -> nat option **)

  let get_num_const =
    get_num_var

  (** val divide_in_cs' :
      char list list list -> char list list -> char list list -> char list
      list list **)

  let rec divide_in_cs' final act = function
  | [] -> final
  | x_0::xs ->
    if eqb0 x_0 (';'::[])
    then divide_in_cs' (app final (act::[])) [] xs
    else divide_in_cs' final (app act (x_0::[])) xs

  (** val divide_in_cs : char list list -> char list list list **)

  let divide_in_cs x =
    divide_in_cs' [] [] x

  (** val map_list :
      (char list list -> z list) -> char list list list -> z list list **)

  let map_list =
    map

  (** val my_of_list_Z : nat -> z list -> z t option **)

  let rec my_of_list_Z n0 = function
  | [] -> (match n0 with
           | O -> Some (const Z0 O)
           | S _ -> None)
  | x::xs ->
    (match n0 with
     | O -> None
     | S n' ->
       (match my_of_list_Z n' xs with
        | Some v -> Some (Cons (x, n', v))
        | None -> None))

  (** val my_of_list_cs :
      nat -> nat -> constraint0 list -> constraint0 t option **)

  let rec my_of_list_cs n_var n0 = function
  | [] -> (match n0 with
           | O -> Some (const (const Z0 n_var) n0)
           | S _ -> None)
  | x::xs ->
    (match n0 with
     | O -> None
     | S n' ->
       (match my_of_list_cs n_var n' xs with
        | Some v -> Some (Cons (x, n', v))
        | None -> None))

  (** val ensure_c : nat -> z list -> constraint0 option **)

  let ensure_c n_var x =
    my_of_list_Z (S (add n_var n_var)) x

  (** val ensure_cs' :
      nat -> nat -> constraint0 list -> z list list -> constraints option **)

  let rec ensure_cs' n_var n_c res = function
  | [] -> my_of_list_cs (S (add n_var n_var)) n_c res
  | x'::xs ->
    let opt_c = ensure_c n_var x' in
    (match opt_c with
     | Some c -> ensure_cs' n_var n_c (app res (c::[])) xs
     | None -> None)

  (** val ensure_cs : nat -> nat -> z list list -> constraints option **)

  let ensure_cs n_var n_c x =
    ensure_cs' n_var n_c [] x

  (** val get_cs : nat -> nat -> char list list -> constraints option **)

  let get_cs n_var n_c x =
    ensure_cs n_var n_c (map_list parseZList (divide_in_cs x))

  (** val ensure_func : nat -> z list -> lex_function option **)

  let ensure_func n_var x =
    my_of_list_Z (S n_var) x

  (** val ensure_lex' :
      nat -> lex_function list -> z list list -> lex_function list option **)

  let rec ensure_lex' n_var res = function
  | [] -> Some res
  | x'::xs ->
    let opt_f = ensure_func n_var x' in
    (match opt_f with
     | Some f -> ensure_lex' n_var (app res (f::[])) xs
     | None -> None)

  (** val ensure_lex : nat -> z list list -> lex_function list option **)

  let ensure_lex n_var x =
    ensure_lex' n_var [] x

  (** val get_lex_func : nat -> char list list -> lex_function list option **)

  let get_lex_func n_var x =
    ensure_lex n_var (map_list parseZList (divide_in_cs x))

  (** val to_pair : nat list list -> (list_d * list_d) list **)

  let rec to_pair = function
  | [] -> []
  | x_1::l ->
    (match l with
     | [] -> []
     | x_2::xs -> app (combine (x_1::[]) (x_2::[])) (to_pair xs))

  (** val ensure_d' :
      nat list list -> nat list list -> nat list list -> (list_d * list_d)
      list option **)

  let rec ensure_d' res aux = function
  | [] ->
    (match aux with
     | [] -> if Nat.even (length res) then Some (to_pair res) else None
     | _::_ -> None)
  | x'::xs ->
    (match aux with
     | [] -> ensure_d' res (app aux (x'::[])) xs
     | _::_ -> ensure_d' (app res (app aux (x'::[]))) [] xs)

  (** val ensure_d : nat list list -> (list_d * list_d) list option **)

  let ensure_d x =
    ensure_d' [] [] x

  (** val get_ds : char list list -> (list_d * list_d) list option **)

  let get_ds x =
    ensure_d (map parseNatList (divide_in_cs x))

  (** val check_loop : char list list list -> bool **)

  let check_loop = function
  | [] -> false
  | x_0::xs0 ->
    let n_var_opt = get_num_var x_0 in
    (match n_var_opt with
     | Some n_var ->
       (match xs0 with
        | [] -> false
        | x_1::xs1 ->
          let n_c_opt = get_num_const x_1 in
          (match n_c_opt with
           | Some n_c ->
             (match xs1 with
              | [] -> false
              | x_2::xs2 ->
                let cs_opt = get_cs n_var n_c x_2 in
                (match cs_opt with
                 | Some cs ->
                   (match xs2 with
                    | [] -> false
                    | x_3::xs3 ->
                      let fs_opt = get_lex_func n_var x_3 in
                      (match fs_opt with
                       | Some fs ->
                         (match xs3 with
                          | [] -> false
                          | x_4::_ ->
                            let ds_opt = get_ds x_4 in
                            (match ds_opt with
                             | Some ds -> is_lex n_var n_c cs fs ds
                             | None -> false))
                       | None -> false))
                 | None -> false))
           | None -> false))
     | None -> false)
 end
