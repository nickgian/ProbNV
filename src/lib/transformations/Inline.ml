(** * Expression inlining functions*)

open ProbNv_lang.Syntax
open ProbNv_datastructures
open ProbNv_lang.Collections
open ProbNv_utils

let is_function_ty e =
  (*implement get inner_Type *)
  let get_inner_type x = x in
  let ty = get_inner_type (ProbNv_utils.OCamlUtils.oget e.ety) in
  match ty.typ with TArrow _ -> Some ty | _ -> None

(* let rec has_var p x =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ -> false
  | PVar y -> Var.equals x y
  | PEdge (p1, p2) -> has_var p1 x || has_var p2 x
  | PTuple ps ->
    BatList.exists (fun p -> has_var p x) ps
  | PRecord map ->
    StringMap.exists (fun _ p -> has_var p x) map
  | POption None -> false
  | POption (Some p) -> has_var p x

let rec remove_all env p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ -> env
  | PVar x -> Env.remove env x
  | PEdge (p1, p2) -> remove_all env (PTuple [p1; p2])
  | PTuple ps ->
    BatList.fold_left (fun acc p -> remove_all acc p) env ps
  | PRecord map ->
    StringMap.fold (fun _ p acc -> remove_all acc p) map env
  | POption None -> env
  | POption (Some p) -> remove_all env p *)

(* Substitutes x in e1 with e2 *)
let rec substitute x e1 e2 =
  match e1.e with
  | EVar y -> if Var.equals x y then e2 else e1
  | EFun f ->
      if Var.equals x f.arg then e1 else efun { f with body = substitute x f.body e2 } |> wrap e1
  | EApp (e3, e4) -> eapp (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | EIf (e3, e4, e5) ->
      eif (substitute x e3 e2) (substitute x e4 e2) (substitute x e5 e2) |> wrap e1
  | ELet (y, e3, e4) ->
      if Var.equals x y then elet y (substitute x e3 e2) e4
      else elet y (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | EOp (op, es) -> eop op (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
  | EVal _ -> e1
  | EBddIf (e3, e4, e5) ->
      ebddIf (substitute x e3 e2) (substitute x e4 e2) (substitute x e5 e2) |> wrap e1
  | EToBdd e3 -> etoBdd (substitute x e3 e2) |> wrap e1
  | EToMap e3 -> etoMap (substitute x e3 e2) |> wrap e1
  | EApplyN (e3, es) ->
      eApplyN (substitute x e3 e2) (BatList.map (fun e -> substitute x e e2) es) |> wrap e1

(* | EMatch (e, bs) ->
     ematch (substitute x e e2)
       (mapBranches (fun (p,e) -> substitute_pattern x e2 (p,e)) bs)
     |> wrap e1
   | ESome e -> esome (substitute x e e2) |> wrap e1
   | ETuple es ->
     etuple (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
   | ERecord map ->
     erecord (StringMap.map (fun e -> substitute x e e2) map) |> wrap e1
   | EProject (e, l) ->
     eproject (substitute x e e2) l *)

(* and substitute_pattern x e2 (p, e) =
  if has_var p x then (p, e) else (p, substitute x e e2) *)

(* Inline applications*)
let rec inline_app cond env e1 e2 : exp =
  let inline_app = inline_app cond in
  let inline_exp = inline_exp cond in
  let exp =
    match e1.e with
    | EVar x -> (
        match Env.lookup_opt env x with None -> eapp e1 e2 | Some e -> inline_app env e e2 )
    | EFun f ->
        if cond (OCamlUtils.oget f.resty) then
          let e = substitute f.arg f.body e2 in
          inline_exp env e
        else eapp (inline_exp env e1) (inline_exp env e2)
    | EIf (e3, e4, e5) ->
        let etrue = inline_app env e4 e2 in
        let efalse = inline_app env e5 e2 in
        eif e3 etrue efalse |> wrap e1
    | ELet (x, e3, e4) ->
        let e5 = inline_exp env (eapp e4 e2 |> wrap e4) in
        elet x e3 e5
    | EApp _ -> eapp e1 e2
    (* | ESome _ | ETuple _  | ERecord _ | EProject _  *)
    | EOp _ | EVal _ ->
        failwith (Printf.sprintf "inline_app: %s" (ProbNv_lang.Printing.exp_to_string e1))
    (* | EMatch (e, bs) ->
         let e = inline_exp env e in
         let branches =
           mapBranches (fun (p,e) -> inline_branch_app env e2 (p,e)) bs
       in
        ematch e branches |> wrap e1 *)
  in
  (* Printf.printf "inline_app e1: %s\ninline_app e2: %s)\n"
     (Printing.exp_to_string e1)
     (Printing.exp_to_string e2) ;
     Printf.printf "result: %s\n\n" (Printing.exp_to_string exp); *)
  exp

and inline_branch_app env e2 (p, e) = (p, inline_app env e e2)

(* inlines expressions *)
and inline_exp (cond : ty -> bool) (env : exp Env.t) (e : exp) : exp =
  let inline_exp = inline_exp cond in
  match e.e with
  | EVar x -> ( match Env.lookup_opt env x with None -> e | Some e1 -> e1 )
  | EVal _ -> e
  | EOp (op, es) -> eop op (BatList.map (inline_exp env) es) |> wrap e
  | EFun f ->
      let body = inline_exp env f.body in
      efun { f with body } |> wrap e
  | EApp (e1, e2) -> inline_app cond env (inline_exp env e1) (inline_exp env e2)
  | EIf (e1, e2, e3) -> eif (inline_exp env e1) (inline_exp env e2) (inline_exp env e3) |> wrap e
  | ELet (x, e1, e2) -> (
      let e1' = inline_exp env e1 in
      (* only inline if condition on type is met *)
      match is_function_ty e1 with
      | Some ty when cond ty -> inline_exp (Env.update env x e1') e2 |> wrap e
      | _ ->
          (* TODO: change this for inlining symbolics *)
          elet x e1' (inline_exp env e2) |> wrap e )
  | EBddIf (e1, e2, e3) ->
      ebddIf (inline_exp env e1) (inline_exp env e2) (inline_exp env e3) |> wrap e
  | EToBdd e1 -> etoBdd (inline_exp env e1) |> wrap e
  | EToMap e1 -> etoMap (inline_exp env e1) |> wrap e
  | EApplyN (e1, es) -> eApplyN (inline_exp env e1) (BatList.map (inline_exp env) es) |> wrap e

(* | ETuple es -> etuple (BatList.map (inline_exp env) es) |> wrap e
   | ERecord map -> erecord (StringMap.map (inline_exp env) map) |> wrap e
   | EProject (e, l) -> eproject (inline_exp env e) l |> wrap e
   | ESome e1 -> esome (inline_exp env e1) |> wrap e
   | EMatch (e1, bs) ->
     ematch (inline_exp env e1)
       (mapBranches (fun (p,e) -> inline_branch env (p,e)) bs)
     |> wrap e
   | ETy (e1, ty) -> ety (inline_exp env e1) ty |> wrap e *)

(* Printf.printf "inline: %s\n" (Printing.exp_to_string e);
   Printf.printf "result: %s\n\n" (Printing.exp_to_string ret); *)

(* TODO: right now this is assuming that patterns won't contain functions
   this will fail for example with an expression like:  Some (fun v -> v) *)
(* and inline_branch env (p, e) =
  let env' = remove_all env p in
  (p, inline_exp env' e) *)

(* Inlines a declaration if predicate [cond] returns true *)
let inline_declaration (cond : ty -> bool) (env : exp Env.t) (d : declaration) =
  let inline_exp = inline_exp cond in
  match d with
  | DLet (x, e) ->
      let e = inline_exp env e in
      if cond (OCamlUtils.oget e.ety) then (Env.update env x e, None) else (env, Some (DLet (x, e)))
  | DSymbolic (x, ty) -> (env, Some (DSymbolic (x, ty)))
  | DAssert e -> (env, Some (DAssert (inline_exp env e)))
  | DSolve { aty; var_names; init; trans; merge } ->
      (* Inline within the functions but don't inline e in future expressions *)
      let init, trans, merge = (inline_exp env init, inline_exp env trans, inline_exp env merge) in
      (env, Some (DSolve { aty; var_names; init; trans; merge }))
  (* | DUserTy _  *)
  | DNodes _ | DEdges _ -> (env, Some d)

let rec inline_declarations_aux cond env (ds : declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' -> (
      let env', d' = inline_declaration cond env d in
      match d' with
      | None -> inline_declarations_aux cond env' ds'
      | Some d' -> d' :: inline_declarations_aux cond env' ds' )

(* Inline everything *)
let inline_declarations (ds : declarations) = inline_declarations_aux (fun _ -> true) Env.empty ds

let rec getReturnType ty = match ty.typ with TArrow (ty1, ty2) -> getReturnType ty2 | _ -> ty

(* Inline functions that return a multivalue *)
let inline_multivalue_declarations (ds : declarations) =
  let rec cond ty =
    match ty.typ with
    | TInt _ | TBool | TEdge | TNode -> false
    | TVar _ | QVar _ -> failwith "QVar/TVar found"
    | TArrow (_, ty2) -> (
        match (getReturnType ty2).mode with
        | Some Multivalue -> true
        | Some _ -> false
        | None -> failwith "No mode found" )
  in
  inline_declarations_aux (fun ty -> cond ty) Env.empty ds

(* match get_attr_type ds with
   | None ->
   failwith "attribute type not declared: type attribute = ..."
   | Some ty -> inline_declarations_aux Env.empty ds *)
