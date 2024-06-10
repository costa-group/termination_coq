
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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

module Nat :
 sig
  val add : nat -> nat -> nat

  val tail_add : nat -> nat -> nat
 end

type 'a t =
| Nil0
| Cons0 of 'a * nat * 'a t

val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2

val hd : nat -> 'a1 t -> 'a1

val const : 'a1 -> nat -> 'a1 t

val tl : nat -> 'a1 t -> 'a1 t

val shiftin : nat -> 'a1 -> 'a1 t -> 'a1 t

val append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t

val rev_append_tail : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t

val rev_append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t

val rev : nat -> 'a1 t -> 'a1 t

val map : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val geb : z -> z -> bool

  val eqb : z -> z -> bool

  val of_nat : nat -> z
 end

type constraint0 = z t

type constraints = constraint0 t

val vect_add : nat -> z t -> z t -> z t

val vect_mul : nat -> nat -> z t -> z t

val vect_mul_Z : nat -> z -> z t -> z t

val comb_conic : nat -> nat -> nat t -> constraints -> z t

val is_gt_on_last : nat -> constraint0 -> constraint0 -> bool

val is_minus_one : nat -> constraint0 -> bool

type lex_function = z t

val c_of_f : nat -> lex_function -> constraint0

val c_of_f' : nat -> lex_function -> constraint0

val cs_f_i_minus_f_i' : nat -> lex_function -> constraint0

val cs_f_i'_minus_f_i : nat -> lex_function -> constraint0

val new_cs : nat -> nat -> constraints -> lex_function -> constraints

type list_d = nat list

val my_of_list : nat -> nat list -> nat t option

val lex_func : nat -> nat -> constraints -> nat t -> constraint0 -> bool

val is_lex :
  nat -> nat -> constraints -> lex_function list -> (list_d, list_d) prod list -> bool
