open Cudd
open ProbNv_datastructures
open ProbNv_lang
open Syntax

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BOption of Bdd.vt * t
  | Tuple of t list

val print : t -> string

val equal_t : t -> t -> bool

val bdd_of_bool : bool -> Cudd.Man.v Cudd.Bdd.t

val create_value : int -> AdjGraph.t -> t
(** Given a type index, creates a BDD value representing all possible values of this type. *)

val toBdd : (int * int -> 'a -> 'b) -> vty_id:int -> 'a -> t
(** Converts a value to a BDD *)

val wrap_mtbdd : t -> bool Mtbdd.t

val ite : t -> t -> t -> t

val eq : t -> t -> t

val add : t -> t -> t

val uand : t -> t -> t

val leq : t -> t -> t

val lt : t -> t -> t

val band : t -> t -> t

val bor : t -> t -> t

val toMap : value:'a -> 'a Cudd.Mtbdd.unique Cudd.Vdd.t

val applyN :
  f:'b ->
  args:'a Cudd.Mtbdd.unique Cudd.Vdd.t array ->
  'a Cudd.Mtbdd.unique Cudd.Vdd.t

  val apply1 :
  op_key:int*'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbdd.unique Cudd.Vdd.t ->
  'd Cudd.Mtbdd.unique Cudd.Vdd.t

  val apply2 :
  op_key:int*'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbdd.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbdd.unique Cudd.Vdd.t ->
  'd Cudd.Mtbdd.unique Cudd.Vdd.t

  val apply3 :
  op_key:int*'f ->
  f:('c -> 'd) ->
  arg1:'x Cudd.Mtbdd.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbdd.unique Cudd.Vdd.t ->
  arg3: 'z Cudd.Mtbdd.unique Cudd.Vdd.t ->
  'a Cudd.Mtbdd.unique Cudd.Vdd.t
