open Cudd
open ProbNv_datastructures
open ProbNv_lang
open Syntax

type 'a t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BOption of Bdd.vt * 'a t
  | Tuple of 'a t list
  | BMap of 'a CompileBDDs.t

val bdd_of_bool : bool -> Cudd.Man.v Cudd.Bdd.t

(* val value_mtbdd_bool_mtbdd
  :  value Cudd.Mtbdd.unique Cudd.Vdd.t
  -> bool Cudd.Mtbdd.unique Cudd.Vdd.t *)

(** Given a type index, creates a BDD value representing all possible values of this type. *)
val create_value : int -> 'a t

(** Converts a value to a BDD *)
val toBdd: (int * int -> 'a -> 'b) -> val_ty_id:int -> 'v -> 'v t

val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
