open Syntax
open Batteries
open ProbNv_datastructures
include ProbNv_utils.PrimitiveCollections

module VarMap = BetterMap.Make(Var)
module VarSet = BetterSet.Make(Var)

module TypeMap = BetterMap.Make (struct
    type t = ty

    let compare = compare
    let to_string = Printing.ty_to_string
  end)

module ValueSet = BetterSet.Make (struct
    type t = value

    let compare v1 v2 = compare v1 v2
    let to_string = Printing.value_to_string ~show_types:false
  end)

module ValueMap = BetterMap.Make (struct
    type t = value

    let compare v1 v2 = compare v1 v2
    let to_string = Printing.value_to_string ~show_types:false
  end)
;;

module ExpMap = BetterMap.Make (struct
    type t = exp

    let compare e1 e2 = compare e1 e2
    let to_string = Printing.exp_to_string ~show_types:false
  end)

module ExpSet = BetterSet.Make (struct
    type t = exp
    let compare = compare_es
    let to_string = Printing.exp_to_string ~show_types:false
  end)

(* module ExpEnvMap = BatMap.Make (struct
    type t = exp * (value Env.t)

    let compare x1 x2 =
      let cmp1 = compare_exps (fst x1) (fst x2) in
      if cmp1 = 0 then Env.compare compare_values (snd x1) (snd x2) else cmp1
  end) *)
