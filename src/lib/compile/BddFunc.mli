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
val create_value : int -> 'a t

(** Converts a value to a BDD *)
val toBdd: (int * int -> 'a -> 'b) -> val_ty_id:int -> 'v -> 'v t

val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t

val ite : 'a t -> 'a t -> 'a t -> 'a t
  
val eq : 'a t -> 'b t -> 'c t

val add : 'a t -> 'b t -> 'c t

val uand : 'a t -> 'b t -> 'c t

val leq : 'a t -> 'b t -> 'c t

val lt : 'a t -> 'b t -> 'c t

val band : 'a t -> 'b t -> 'c t

val toMap: value:'a -> vty_id:int -> 'b CompileBDDs.t

val applyN :
    f:'b ->
    args:'a Cudd.Mtbdd.unique Cudd.Vdd.t array ->
    vty_id:int -> 'a CompileBDDs.t