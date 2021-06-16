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

val create_value : string -> int -> int -> AdjGraph.t -> t list
(** Given a distribution index, a type index, and the topology, creates a BDD
    value representing all possible values of this type. *)

val create_value_expr :
  string -> (t list -> float Cudd.Mtbddc.t) -> int -> AdjGraph.t -> t list
(** Likewise but this is used for distributions defined through a ProbNV expression. In this instance, a function from
    BDDs to distributions describing the user's ProbNV expression is given as argument. *)

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

val bnot : t -> t

val toMap : ?distr:bool -> value:'a -> 'a Cudd.Mtbddc.unique Cudd.Vdd.t

val applyN :
  ?distr:bool ->
  f:'b ->
  args:'a Cudd.Mtbddc.unique Cudd.Vdd.t array ->
  'a Cudd.Mtbddc.unique Cudd.Vdd.t

val apply1 :
  ?distr:bool ->
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'd Cudd.Mtbddc.unique Cudd.Vdd.t

val apply2 :
  ?distr:bool ->
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'c Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'd Cudd.Mtbddc.unique Cudd.Vdd.t

val apply3 :
  ?distr:bool ->
  op_key:int * 'f ->
  f:('c -> 'd) ->
  arg1:'x Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg2:'y Cudd.Mtbddc.unique Cudd.Vdd.t ->
  arg3:'z Cudd.Mtbddc.unique Cudd.Vdd.t ->
  'a Cudd.Mtbddc.unique Cudd.Vdd.t

val bddOps : float ref
