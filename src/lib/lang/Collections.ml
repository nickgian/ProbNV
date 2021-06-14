open Syntax
open Batteries
open ProbNv_datastructures
open ProbNv_utils
include PrimitiveCollections
module VarMap = BetterMap.Make (Var)
module VarSet = BetterSet.Make (Var)

module TypeMap = BetterMap.Make (struct
  type t = ty

  let compare = compare

  let to_string = Printing.ty_to_string ~show_modes:false
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

(** A map over types but only compares the base types *)
module BaseTypeMap = BetterMap.Make (struct
  type t = ty

  let rec compareBase ty1 ty2 =
    match (ty1.typ, ty2.typ) with
    | TBool, TBool | TNode, TNode | TEdge, TEdge -> 0
    | TInt n1, TInt n2 -> compare n1 n2
    | TArrow (t1, t2), TArrow (s1, s2) ->
        let r1 = compareBase t1 s1 in
        if r1 = 0 then compareBase t2 s2 else r1
    | TVar t1, TVar t2 -> (
        match (!t1, !t2) with
        | Unbound (n1, x1), Unbound (n2, x2) ->
            let r1 = Var.compare n1 n2 in
            if r1 = 0 then compare x1 x2 else r1
        | Link t1, Link t2 -> compareBase t1 t2
        | _ -> compare ty1 ty2 )
    | QVar n1, QVar n2 -> Var.compare n1 n2
    | x, y -> compare x y

  let compare = compareBase

  let to_string = Printing.ty_to_string ~show_modes:false
end)

module TypeIds = ArrayIdMake (TypeMap)
module ExpIds = ArrayIdMake (ExpMap)

module DistMap = BetterMap.Make (struct
  type t = distributionExpression

  let compare e1 e2 = compare e1 e2

  let to_string e =
    match e with
    | Uniform -> ""
    | DExpr e -> Printing.distrExpr_to_string e
    | Expr e -> Printing.exp_to_string e
end)

module DistrIds = ArrayIdMake (DistMap)

(* module ExpEnvMap = BatMap.Make (struct
    type t = exp * (value Env.t)

    let compare x1 x2 =
      let cmp1 = compare_exps (fst x1) (fst x2) in
      if cmp1 = 0 then Env.compare compare_values (snd x1) (snd x2) else cmp1
  end) *)
