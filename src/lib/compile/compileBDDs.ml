open ProbNv_lang
open Syntax
open Cudd

(* BddMap plus the type of the values and the range of BDD variables used to represent the map*)
type 'a t = {
  bdd : 'a Mtbddc.t;
  key_ty_id : int;
  val_ty_id : int;
  var_range : int * int;
}

(** ** Support for MapIf*)

(* Expression map cache used to avoid recompiling mapIf predicates. First
   element of the value is the bdd, second one is the identifier used to look it
   up in the native BDDs module *)

let bddfunc_store = Collections.ExpIds.create ()

let pred_store = Collections.ExpIds.create ()

let type_store = Collections.TypeIds.create ()

let exp_store = Collections.ExpIds.create ()

let distr_store = Collections.DistrIds.create ()

(* Helper function that canonicalizes (removing TLinks) types before generating an id *)
let get_fresh_type_id store typ =
  let typ = Typing.canonicalize_type typ in
  Collections.TypeIds.fresh_id store typ
