From Coq Require Import Numbers.DecimalString.
From Coq Require Import Numbers.HexadecimalNat.
From Coq Require Import ZArith.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
Require Import Hexadecimal HexadecimalFacts Arith.
Require Import Coq.NArith.NArith.
Require Import Vector.
From Coq Require Import Lists.List. Import ListNotations.

Require Import constraint.
Require Import checker.

Module Parser.

Definition isWhite (c : ascii) : bool :=
  let n := N_of_ascii c in
  orb (orb (N.eqb n 32%N)   (* space *)
           (N.eqb n 9%N))   (* tab *)
      (orb (N.eqb n 10%N)   (* linefeed *)
           (N.eqb n 13%N)). (* Carriage return. *)

Inductive chartype := white | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else 
    other.


Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).

Fixpoint parseDecNumber' (x : list ascii) (acc : nat) :=
  match x with
  | [] => Some acc
  | d::ds => let n := nat_of_ascii d in
             if (andb (Nat.leb 48 n) (Nat.leb n 57)) then
               parseDecNumber' ds (10*acc+(n-48))
             else None
  end.

Definition parseDecNumber (x : string) : option nat :=
  parseDecNumber' (list_of_string x) 0.

Fixpoint parseNatList (x : list string) : list nat :=
  match x with
  | [] => []
  | x_0::xs => let num := (parseDecNumber x_0) in
               match num with
               | Some z_0 => z_0::(parseNatList xs)
               | None => []
               end  
  end.

Fixpoint parseZList (x : list string) : list Z :=
  match x with
  | [] => []
  | x_0::xs => if ((substring 0 1 x_0) =? "-"%string)%string then
                 let n_x_0 := substring 1 ((String.length x_0) - 1) x_0 in
                 let num := (parseDecNumber n_x_0) in
                 match num with
                 | Some z_0 => (Z.opp (Z.of_nat z_0))::(parseZList xs)
                 | None => []
                 end
               else
                 let num := (parseDecNumber x_0) in
                 match num with
                 | Some z_0 => (Z.of_nat z_0)::(parseZList xs)
                 | None => []
                 end
  end.

Definition get_num_var (x : list string) : option nat :=
  match parseNatList x with
  | [] => None
  | x_0::[] => Some x_0
  | _ => None
  end.

Definition get_num_const (x : list string) : option nat :=
  get_num_var x.

Fixpoint divide_in_cs' (final : list (list string)) (act x : list string) : list (list string) :=
  match x with
  | [] => final
  | x_0::xs => if (x_0 =? ";")%string then divide_in_cs' (final ++ [act]) [] xs else divide_in_cs' final (act ++ [x_0]) xs
  end.

Definition divide_in_cs (x : list string) : list (list string):=
  divide_in_cs' [] [] x.

Definition map_list (f : list string -> list Z) (l : list (list string)) := map f l.


Import VectorNotations.
Local Open Scope vector_scope.
Open Scope Z_scope.

Fixpoint my_of_list_Z (n : nat) (l: list Z) : option (t Z n) :=
  match l with
  | []%list =>
      match n with
      | O => Some (const 0 0)
      | _ => None
      end
  | (x::xs)%list =>
      match n with
      | O => None
      | S n' => match my_of_list_Z n' xs with
                | None => None
                | Some v => Some (x::v)
                end
      end
  end.

Fixpoint my_of_list_cs (n_var n : nat) (l:  list (@constraint n_var)) : option (t (@constraint n_var) n) :=
  match l with
  | []%list =>
      match n with
      | O => Some (const (const 0 n_var) n)
      | _ => None
      end
  | (x::xs)%list =>
      match n with
      | O => None
      | S n' => match my_of_list_cs n_var n' xs with
                | None => None
                | Some v => Some (x::v)
                end
      end
  end.

Local Close Scope vector_scope.

Definition ensure_c (n_var : nat) (x : list Z) : option (@constraint (S (n_var + n_var))) :=
  my_of_list_Z (S (n_var + n_var)) x.
  
Fixpoint ensure_cs' (n_var n_c : nat) (res : list (@constraint (S (n_var + n_var)))) (x : list (list Z)) : option (@constraints (S (n_var + n_var)) n_c) :=
  match x with
  | [] => (my_of_list_cs (S (n_var + n_var)) n_c res)
  | x'::xs => let opt_c := ensure_c n_var x' in
              match opt_c with
              | None => None
              | Some c => ensure_cs' n_var n_c (res ++ [c]) xs
              end
  end.
    
Definition ensure_cs (n_var n_c : nat) (x : list (list Z)) : option (@constraints (S (n_var + n_var)) n_c) :=
  ensure_cs' n_var n_c [] x.
                                                                                                                                 
Definition get_cs (n_var n_c : nat) (x : list string) : option (@constraints (S (n_var + n_var)) n_c) :=
  ensure_cs n_var n_c (map_list parseZList (divide_in_cs x)).

Definition ensure_func (n_var : nat) (x : list Z) : option (@lex_function n_var) :=
  my_of_list_Z (S n_var) x.

Fixpoint ensure_lex' (n_var : nat) (res : list (@lex_function n_var)) (x : list (list Z)) : option (list (@lex_function n_var)) :=
  match x with
  | [] => Some res
  | x'::xs => let opt_f := ensure_func n_var x' in
              match opt_f with
              | None => None
              | Some f => ensure_lex' n_var (res ++ [f]) xs
              end
  end.

Definition ensure_lex (n_var : nat) (x : list (list Z)) : option (list (@lex_function n_var)) :=
  ensure_lex' n_var [] x.

Definition get_lex_func (n_var : nat) (x : list string) : option (list (@lex_function n_var)) :=
  ensure_lex n_var (map_list parseZList (divide_in_cs x)).


Fixpoint to_pair (x : list (list nat)) : list (list_d*list_d):=
  match x with
  | [] => []
  | x'::[] => []
  | x_1::x_2::xs => (List.combine [x_1] [x_2]) ++ (to_pair xs)
  end.


Fixpoint ensure_d' (res aux x : list (list nat)) : option (list ((list_d)*(list_d))) :=
  match x with
  | [] => match aux with
          | [] => if (Nat.even (List.length res)) then Some (to_pair res) else None
          | _ => None
          end
  | x'::xs => match aux with
              | [] => ensure_d' res (aux++[x']) xs
              | _ => ensure_d' (res++aux++[x']) [] xs
              end       
end.



Definition ensure_d (x : list (list nat)) : option (list ((list_d)*(list_d))) :=
  ensure_d' [] [] x.

Definition get_ds (x : list string) : option (list ((list_d)*(list_d))) :=
  ensure_d (List.map parseNatList (divide_in_cs x)).

Definition check_loop (x : list (list string)) : bool :=
  match x with
  | [] => false
  | x_0::xs0 => let n_var_opt : option nat := get_num_var x_0 in
                match n_var_opt with
                | None => false
                | Some n_var => match xs0 with
                                | [] => false
                                | x_1::xs1 => let n_c_opt : option nat := get_num_const x_1 in
                                              match n_c_opt with
                                              | None => false
                                              | Some n_c => match xs1 with
                                                            | [] => false
                                                            | x_2::xs2 => let cs_opt : option (@constraints (S (n_var + n_var)) n_c) := get_cs n_var n_c x_2 in
                                                                          match cs_opt with
                                                                          | None => false
                                                                          | Some cs =>
                                                                              match xs2 with
                                                                              | [] => false
                                                                              | x_3::xs3 => let fs_opt : option (list lex_function):= get_lex_func n_var x_3 in
                                                                                            match fs_opt with
                                                                                            | None => false
                                                                                            | Some fs => match xs3 with
                                                                                                         | [] => false
                                                                                                         | x_4::xs4 => let ds_opt : option (list (list_d*list_d)) := get_ds x_4 in
                                                                                                                       match ds_opt with
                                                                                                                       | None => false
                                                                                                                       | Some ds => (@is_lex n_var n_c cs fs ds)
                                                                                                                       end
                                                                                                         end
                                                                                            end
                                                                              end
                                                                          end
                                                            end
                                              end
                                end
                end
  end.


(*Some examples to ensure everything works smoothly*)

(*
Compute lex_func [[1; 0; 0];[1; -1; -1]]%vector [1%nat; 0%nat]%vector (c_of_f [1; 0]%vector).

Compute (@is_lex 1 2 [[1; 0; 0];[1; -1; -1]]%vector [[1;0]%vector] [([1%nat; 0%nat], [0%nat;1%nat]); ([0%nat;1%nat;1%nat;0%nat], [0%nat;0%nat;0%nat;0%nat])]).
 

Compute check_loop [(tokenize "3 ; ");
                    (tokenize "7 ; ");
                    (tokenize " 1  0  0  0  0  0  0 ;
                                0  1  0  0  0  0  0 ;
                                1  0  1  0  0  0  0 ;
                                1 -1  0  0  1  0  0 ;
                               -1  1  0  0 -1  0  0 ;
                               -1  0 -1  0  0  1  2 ;
                                1  0  1  0  0 -1 -2 ; ") ;
                    (tokenize " 0  1  0  0 ;
                                0  0  1  0 ;") ;
                    (tokenize " 0 1 0 0 0 0 0 ;
                                1 0 0 0 1 0 0 ;
                                0 0 1 0 1 0 0 1 0 ;
                                0 0 0 0 1 0 1 1 0 ;
                                0 0 0 0 1 0 1 1 0 1 0 ;
                                0 0 0 0 0 0 0 0 0 0 0 ;")].
*)
End Parser.
