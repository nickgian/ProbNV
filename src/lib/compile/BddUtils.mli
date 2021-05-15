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

type symbolic_var = string * int * int * ProbNv_lang.Syntax.ty * distribution

val vars_list : symbolic_var list ref

val push_symbolic_vars : symbolic_var -> unit
(** Push a new symbolic variable (BDD variables range, type and distribution) to the top of the list *)

val freshvar : unit -> Cudd.Man.v Cudd.Bdd.t

val getVarsNb : unit -> int

val tbool_to_bool : Cudd.Man.tbool -> bool

val tbool_to_obool : Cudd.Man.tbool -> bool option

val computeTrueProbabilityOld :
  bool Cudd.Mtbddc.t ->
  (string * int * int * ProbNv_lang.Syntax.ty * float Cudd.Mtbddc.t) list ->
  float

val createDistributionMap :
  symbolic_var list -> (int * int * distribution) BatMap.Int.t

val computeTrueProbability :
  bool Cudd.Mtbddc.t ->
  (int * int * float Cudd.Mtbddc.t) BatMap.Int.t ->
  Cudd.Bdd.vt option ->
  float

val computeTrueProbabilityBDD :
  bool Cudd.Mtbddc.t -> float Cudd.Mtbddc.t BatMap.Int.t -> float

val generateSat : bool Cudd.Mtbddc.t -> symbolic_var list -> unit

val get_statistics : unit -> unit
