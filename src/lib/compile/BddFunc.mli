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

val create_value : int -> AdjGraph.t -> t
(** Given a type index, creates a BDD value representing all possible values of this type. *)

val toBdd : (int * int -> 'a -> 'b) -> vty_id:int -> 'a -> t
(** Converts a value to a BDD *)

val wrap_mtbdd : t -> bool Mtbddc.t

val ite : t -> t -> t -> t

val eq : t -> t -> t

val add : t -> t -> t

val uand : t -> t -> t

val leq : t -> t -> t

val lt : t -> t -> t

val band : t -> t -> t

val bor : t -> t -> t

val toMap : value:'a -> 'a Cudd.Mtbddc.unique Cudd.Vdd.t

val applyN :
  f:'b ->
  args:'a Cudd.Mtbddc.unique Cudd.Vdd.t array ->
  'a Cudd.Mtbddc.unique Cudd.Vdd.t

val apply1 :
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'd Cudd.Mtbddc.unique Cudd.Vdd.t

val apply2 :
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'd Cudd.Mtbddc.unique Cudd.Vdd.t

val apply3 :
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'x Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg3:'z Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'a Cudd.Mtbddc.unique Cudd.Vdd.t

val apply2_time : float ref

val apply3_time : float ref
