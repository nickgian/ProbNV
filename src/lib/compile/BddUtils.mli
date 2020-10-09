open ProbNv_datastructures
open ProbNv_lang
open Cudd

(** BDD/MTBDD manager *)
val mgr : Cudd.Man.v Cudd.Man.t

val tbl : 'a Cudd.Mtbdd.table

val tbl_bool : bool Cudd.Mtbdd.table

(* Given a type returns the number of decision variables required to represent its values *)
val ty_to_size : Syntax.ty -> int

(** Sets number of variables in the manager *)
val set_size : int -> unit

(** [ithvar i] returns decision variable i from the manager *)
val ithvar : int -> Cudd.Man.v Cudd.Bdd.t

(** Given an integer n and an int i returns the ith-bit of n. *)
val get_bit : int -> int -> bool

val tbool_to_bool : Cudd.Man.tbool -> bool
val tbool_to_obool : Cudd.Man.tbool -> bool option
val count_tops : Cudd.Man.tbool array -> int -> int
val expand : Cudd.Man.tbool list -> int -> Cudd.Man.tbool list list
