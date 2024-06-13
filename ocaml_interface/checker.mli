
type nat =
| O
| S of nat

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool

  val even : nat -> bool
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

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module N :
 sig
  val add : n -> n -> n

  val mul : n -> n -> n

  val eqb : n -> n -> bool

  val to_nat : n -> nat
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

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

  val ltb : z -> z -> bool

  val geb : z -> z -> bool

  val eqb : z -> z -> bool

  val of_nat : nat -> z
 end

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> nat

val eqb0 : char list -> char list -> bool

val length0 : char list -> nat

val substring : nat -> nat -> char list -> char list

type 'a t =
| Nil
| Cons of 'a * nat * 'a t

val rectS :
  ('a1 -> 'a2) -> ('a1 -> nat -> 'a1 t -> 'a2 -> 'a2) -> nat -> 'a1 t -> 'a2

val caseS : ('a1 -> nat -> 'a1 t -> 'a2) -> nat -> 'a1 t -> 'a2

val hd : nat -> 'a1 t -> 'a1

val last : nat -> 'a1 t -> 'a1

val const : 'a1 -> nat -> 'a1 t

val tl : nat -> 'a1 t -> 'a1 t

val shiftin : nat -> 'a1 -> 'a1 t -> 'a1 t

val append : nat -> nat -> 'a1 t -> 'a1 t -> 'a1 t

val map0 : ('a1 -> 'a2) -> nat -> 'a1 t -> 'a2 t

type constraint0 = z t

type constraints = constraint0 t

val vect_add : nat -> z t -> z t -> z t

val vect_mul : nat -> nat -> z t -> z t

val vect_mul_Z : nat -> z -> z t -> z t

val comb_conic : nat -> nat -> nat t -> constraints -> z t

val is_ge_on_last : nat -> constraint0 -> constraint0 -> bool

val is_minus : nat -> constraint0 -> bool

type lex_function = z t

val without_last : nat -> z t -> z t

val c_of_f : nat -> lex_function -> constraint0

val c_of_f' : nat -> lex_function -> constraint0

val cs_f_i_minus_f_i' : nat -> lex_function -> constraint0

val cs_f_i'_minus_f_i : nat -> lex_function -> constraint0

val new_cs : nat -> nat -> constraints -> lex_function -> constraints

type list_d = nat list

val my_of_list : nat -> nat list -> nat t option

val lex_func : nat -> nat -> constraints -> nat t -> constraint0 -> bool

val is_lex :
  nat -> nat -> constraints -> lex_function list -> (list_d * list_d) list ->
  bool

module Parser :
 sig
  val isWhite : char -> bool

  type chartype =
  | Coq_white
  | Coq_other

  val chartype_rect : 'a1 -> 'a1 -> chartype -> 'a1

  val chartype_rec : 'a1 -> 'a1 -> chartype -> 'a1

  val classifyChar : char -> chartype

  val list_of_string : char list -> char list

  val string_of_list : char list -> char list

  type token = char list

  val tokenize_helper : chartype -> char list -> char list -> char list list

  val tokenize : char list -> char list list

  val parseDecNumber' : char list -> nat -> nat option

  val parseDecNumber : char list -> nat option

  val parseNatList : char list list -> nat list

  val parseZList : char list list -> z list

  val get_num_var : char list list -> nat option

  val get_num_const : char list list -> nat option

  val divide_in_cs' :
    char list list list -> char list list -> char list list -> char list list
    list

  val divide_in_cs : char list list -> char list list list

  val map_list :
    (char list list -> z list) -> char list list list -> z list list

  val my_of_list_Z : nat -> z list -> z t option

  val my_of_list_cs : nat -> nat -> constraint0 list -> constraint0 t option

  val ensure_c : nat -> z list -> constraint0 option

  val ensure_cs' :
    nat -> nat -> constraint0 list -> z list list -> constraints option

  val ensure_cs : nat -> nat -> z list list -> constraints option

  val get_cs : nat -> nat -> char list list -> constraints option

  val ensure_func : nat -> z list -> lex_function option

  val ensure_lex' :
    nat -> lex_function list -> z list list -> lex_function list option

  val ensure_lex : nat -> z list list -> lex_function list option

  val get_lex_func : nat -> char list list -> lex_function list option

  val to_pair : nat list list -> (list_d * list_d) list

  val ensure_d' :
    nat list list -> nat list list -> nat list list -> (list_d * list_d) list
    option

  val ensure_d : nat list list -> (list_d * list_d) list option

  val get_ds : char list list -> (list_d * list_d) list option

  val check_loop : char list list list -> bool
 end
