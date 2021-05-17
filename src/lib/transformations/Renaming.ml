open ProbNv_lang
open ProbNv_datastructures
open Syntax
open Collections

(* Maps fresh names back to the original names *)
let map_back bmap new_name old_name =
  bmap := Collections.VarMap.add new_name old_name !bmap

(* TODO: Make sure this doesn't have to be Var.to_string *)
let fresh x = Var.fresh (Var.name x)

let rec rename_solve_vars bmap env e =
  match e.e with
  | EVar x ->
      let y = fresh x in
      map_back bmap y x;
      let env = Env.update env x y in
      (env, evar y |> wrap e)
  | _ -> failwith "Bad DSolve"

let rec update_pattern (env : Var.t Env.t) (p : pattern) : pattern * Var.t Env.t
    =
  match p with
  | PWild | PBool _ | PInt _ | PNode _ | PEdgeId _ -> (p, env)
  | PVar x ->
      let y = fresh x in
      (PVar y, Env.update env x y)
  | PEdge (p1, p2) ->
      let p1', env = update_pattern env p1 in
      let p2', env = update_pattern env p2 in
      (PEdge (p1', p2'), env)
  | PTuple ps ->
      let env, ps = BatList.fold_left add_pattern (env, []) ps in
      (PTuple (BatList.rev ps), env)
  | POption None -> (p, env)
  | POption (Some p) ->
      let p', env = update_pattern env p in
      (POption (Some p'), env)
  | PRecord map ->
      let env, map =
        StringMap.fold
          (fun k p (env, acc) ->
            let p', env' = update_pattern env p in
            (env', StringMap.add k p' acc))
          map (env, StringMap.empty)
      in
      (PRecord map, env)

and add_pattern (env, ps) p =
  let p', env' = update_pattern env p in
  (env', p' :: ps)

let rec alpha_convert_exp (env : Var.t Env.t) (e : exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e);
     Printf.printf "type: %s\n" (Printing.ty_to_string (oget e.ety)); *)
  match e.e with
  | EVar x -> evar (Env.lookup env x) |> wrap e
  | EVal _ -> e
  | EOp (op, es) ->
      eop op (BatList.map (fun e -> alpha_convert_exp env e) es) |> wrap e
  | EFun f ->
      let x = fresh f.arg in
      let e' = alpha_convert_exp (Env.update env f.arg x) f.body in
      efun { f with arg = x; body = e' } |> wrap e
  | EApp (e1, e2) ->
      eapp (alpha_convert_exp env e1) (alpha_convert_exp env e2) |> wrap e
  | EIf (e1, e2, e3) ->
      eif (alpha_convert_exp env e1) (alpha_convert_exp env e2)
        (alpha_convert_exp env e3)
      |> wrap e
  | ELet (x, e1, e2) ->
      let e1' = alpha_convert_exp env e1 in
      let y = fresh x in
      let e2' = alpha_convert_exp (Env.update env x y) e2 in
      elet y e1' e2' |> wrap e
  | EBddIf (e1, e2, e3) ->
      ebddIf (alpha_convert_exp env e1) (alpha_convert_exp env e2)
        (alpha_convert_exp env e3)
      |> wrap e
  | EToBdd e1 -> etoBdd (alpha_convert_exp env e1) |> wrap e
  | EToMap e1 -> etoMap (alpha_convert_exp env e1) |> wrap e
  | EApplyN (e1, es) ->
      eApplyN (alpha_convert_exp env e1)
        (BatList.map (fun e -> alpha_convert_exp env e) es)
      |> wrap e
  | ETuple es ->
      etuple (BatList.map (fun e -> alpha_convert_exp env e) es) |> wrap e
  | EMatch (e1, bs) ->
      let bs' =
        mapBranches
          (fun (p, ep) ->
            let p, env = update_pattern env p in
            (p, alpha_convert_exp env ep))
          bs
      in
      ematch (alpha_convert_exp env e1) bs' |> wrap e
  | ESome e1 -> esome (alpha_convert_exp env e1) |> wrap e
  | ERecord map ->
      erecord (StringMap.map (fun e -> alpha_convert_exp env e) map) |> wrap e
  | EProject (e, l) -> eproject (alpha_convert_exp env e) l |> wrap e

let alpha_convert_declaration bmap (env : Var.t Env.t) (d : declaration) =
  match d with
  | DLet (x, e) ->
      let y = fresh x in
      let e = alpha_convert_exp env e in
      let env = Env.update env x y in
      (env, DLet (y, e))
  | DSymbolic (x, ty, p) ->
      let y = fresh x in
      map_back bmap y x;
      let env = Env.update env x y in
      (env, DSymbolic (y, ty, p))
  | DSolve { aty; var_names; init; trans; merge } ->
      let init, trans, merge =
        ( alpha_convert_exp env init,
          alpha_convert_exp env trans,
          alpha_convert_exp env merge )
      in
      let env, y = rename_solve_vars bmap env var_names in
      (env, DSolve { aty; var_names = y; init; trans; merge })
  | DForward
      { names_V; names_E; fwdInit; fwdOut; fwdIn; hinitV; hinitE; logE; logV }
    ->
      let fwdInit, fwdOut, fwdIn, hinitV, hinitE, logE, logV =
        ( alpha_convert_exp env fwdInit,
          alpha_convert_exp env fwdOut,
          alpha_convert_exp env fwdIn,
          alpha_convert_exp env hinitV,
          alpha_convert_exp env hinitE,
          alpha_convert_exp env logE,
          alpha_convert_exp env logV )
      in
      let env, names_V = rename_solve_vars bmap env names_V in
      let env, names_E = rename_solve_vars bmap env names_E in
      ( env,
        DForward
          {
            names_V;
            names_E;
            fwdInit;
            fwdOut;
            fwdIn;
            hinitV;
            hinitE;
            logE;
            logV;
          } )
  | DAssert (name, e, prob, None) ->
      (env, DAssert (name, alpha_convert_exp env e, prob, None))
  | DAssert (name, e, prob, Some c) ->
      ( env,
        DAssert
          (name, alpha_convert_exp env e, prob, Some (alpha_convert_exp env c))
      )
  | DUserTy _ | DNodes _ | DEdges _ -> (env, d)

let rec alpha_convert_aux bmap env (ds : declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = alpha_convert_declaration bmap env d in
      d' :: alpha_convert_aux bmap env' ds'

let update_symbolics bmap smap =
  let open Collections in
  List.map
    (fun (s, v) ->
      match VarMap.Exceptionless.find s bmap with
      | None -> (s, v)
      | Some k -> (k, v))
    smap

let adjust_solution bmap (s : ProbNv_solution.Solution.t) =
  { s with solves = update_symbolics bmap s.solves }

let rec alpha_convert_declarations (ds : declarations) =
  (* Var.reset () ; *)
  let bmap = ref Collections.VarMap.empty in
  let prog = alpha_convert_aux bmap Env.empty ds in
  (prog, adjust_solution !bmap)
