open ProbNv_datastructures
open ProbNv_lang
open Cudd

type distribution = float Mtbddc.t

val bdd_of_bool : bool -> Cudd.Man.v Cudd.Bdd.t
(** Convert bool to bdd *)

val mgr : Cudd.Man.v Cudd.Man.t
(** BDD/MTBDD manager *)

val set_reordering : int option -> unit

val tbl : 'a Cudd.Mtbddc.table

val tbl_probabilities : float Cudd.Mtbddc.table

val tbl_nv : Syntax.value Cudd.Mtbddc.table

(* 
val tbl_bool : bool Cudd.Mtbddc.table *)

(* Given a type returns the number of decision variables required to represent its values *)
val ty_to_size : Syntax.ty -> int

val vars_list : (int * int * Syntax.ty * distribution) list ref

val push_symbolic_vars :
  int * int * ProbNv_lang.Syntax.ty * distribution -> unit
(** Push a new symbolic variable (BDD variables range, type and distribution) to the top of the list *)

val freshvars : ProbNv_lang.Syntax.ty -> int * int * Cudd.Man.v Cudd.Bdd.t array
(** [freshvars ty] returns the decision variables necessary to represent this type *)

val freshvar : unit -> Cudd.Man.v Cudd.Bdd.t

val getVarsNb : unit -> int

val tbool_to_bool : Cudd.Man.tbool -> bool

val tbool_to_obool : Cudd.Man.tbool -> bool option

val computeTrueProbabilityOld :
  bool Cudd.Mtbddc.t ->
  (int * int * ProbNv_lang.Syntax.ty * float Cudd.Mtbddc.t) list ->
  float

val computeTrueProbability :
  bool Cudd.Mtbddc.t ->
  (int * int * ProbNv_lang.Syntax.ty * float Cudd.Mtbddc.t) list ->
  float

val computeTrueProbabilityBDD :
  bool Cudd.Mtbddc.t -> float Cudd.Mtbddc.t BatMap.Int.t -> float

val get_statistics : unit -> unit
