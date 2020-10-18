open ProbNv_datastructures
open ProbNv_lang
open Cudd

type distribution = float Mtbdd.t

(** BDD/MTBDD manager *)
val mgr : Cudd.Man.v Cudd.Man.t

val tbl : 'a Cudd.Mtbdd.table

val tbl_nv : Syntax.value Cudd.Mtbdd.table

val tbl_probabilities : float Cudd.Mtbdd.table

(* 
val tbl_bool : bool Cudd.Mtbdd.table *)

(* Given a type returns the number of decision variables required to represent its values *)
val ty_to_size : Syntax.ty -> int

val vars_list : (int * int * Syntax.ty * distribution) list ref

(** Push a new symbolic variable (BDD variables range, type and distribution) to the top of the list *)
val push_symbolic_vars: int * int * ProbNv_lang.Syntax.ty * distribution -> unit

(** [freshvars ty] returns the decision variables necessary to represent this type *)
val freshvars: ProbNv_lang.Syntax.ty -> int * int * Cudd.Man.v Cudd.Bdd.t array

(** Given an integer n and an int i returns the ith-bit of n. *)
val get_bit : int -> int -> bool

val tbool_to_bool : Cudd.Man.tbool -> bool

val tbool_to_obool : Cudd.Man.tbool -> bool option

val computeTrueProbability: bool Cudd.Mtbdd.t -> (int * int * ProbNv_lang.Syntax.ty * float Cudd.Mtbdd.t) list -> float