open Cudd
open ProbNv_datastructures
open ProbNv_lang
open Syntax

type 'a t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BOption of Bdd.vt * 'a t
  | Tuple of 'a t list

val print : 'a t -> string

val equal_t : 'a t -> 'b t -> bool

val bdd_of_bool : bool -> Cudd.Man.v Cudd.Bdd.t

(** Given a type index, creates a BDD value representing all possible values of this type. *)
val create_value : int -> AdjGraph.t -> 'a t

val toBdd : (int * int -> 'a -> 'b) -> vty_id:int -> 'v -> 'v t
(** Converts a value to a BDD *)

val wrap_mtbdd : 'a t -> bool Mtbdd.t

val ite : 'a t -> 'a t -> 'a t -> 'a t

val eq : 'a t -> 'b t -> 'c t

val add : 'a t -> 'b t -> 'c t

val uand : 'a t -> 'b t -> 'c t

val leq : 'a t -> 'b t -> 'c t

val lt : 'a t -> 'b t -> 'c t

val band : 'a t -> 'b t -> 'c t

val toMap : value:'a -> 'a Cudd.Mtbdd.unique Cudd.Vdd.t

val applyN :
  f:'b ->
  args:'a Cudd.Mtbdd.unique Cudd.Vdd.t array ->
  'a Cudd.Mtbdd.unique Cudd.Vdd.t
