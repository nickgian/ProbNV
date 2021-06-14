open Batteries
open ProbNv_lang
open Syntax
open Collections
open ProbNv_datastructures
open AdjGraph
open ProbNv_utils.OCamlUtils
open ProbNv_solution
open ProbNv_compile

type recursors = {
  recurse_ty : ty -> ty;
  recurse_pattern : pattern -> ty -> pattern;
  recurse_value : value -> value;
  recurse_exp : exp -> exp;
}

type 'a transformer = recursors -> 'a -> 'a option

type pattern_transformer = recursors -> pattern -> ty -> pattern option

type map_back_transformer =
  (value -> ty -> value) -> Solution.t -> value -> ty -> value option

type 'a toplevel_transformer =
  name:string ->
  ty transformer ->
  pattern_transformer ->
  value transformer ->
  exp transformer ->
  map_back_transformer ->
  'a ->
  'a * Solution.map_back

type transformers = {
  ty_transformer : ty transformer;
  pattern_transformer : pattern_transformer;
  value_transformer : value transformer;
  exp_transformer : exp transformer;
}

let rec build_recursors ~(name : string) (transformers : transformers) :
    recursors =
  {
    recurse_ty = transform_ty ~name transformers;
    recurse_pattern = transform_pattern ~name transformers;
    recurse_value = transform_value ~name transformers;
    recurse_exp = transform_exp ~name transformers;
  }

and transform_ty ~(name : string) (transformers : transformers) (ty : ty) : ty =
  let recursors = build_recursors ~name transformers in
  let transform_ty = recursors.recurse_ty in
  let ty_transformer = transformers.ty_transformer recursors in
  match ty_transformer ty with
  | Some ty -> ty
  | None -> (
      match ty.typ with
      | TBool | TInt _ | TNode | TEdge | TFloat -> ty
      | TOption ty1 -> { ty with typ = TOption (transform_ty ty1) }
      | TTuple tys -> { ty with typ = TTuple (List.map transform_ty tys) }
      | TRecord map ->
          { ty with typ = TRecord (StringMap.map transform_ty map) }
      | TArrow (ty1, ty2) ->
          { ty with typ = TArrow (transform_ty ty1, transform_ty ty2) }
      | TMap (kty, vty) ->
          { ty with typ = TMap (transform_ty kty, transform_ty vty) }
      | TVar { contents = Link ty1 } -> transform_ty ty1
      | TVar _ | QVar _ ->
          failwith @@ name ^ ": transform_ty: encountered TVar or QVar" )

and transform_pattern ~(name : string) (transformers : transformers)
    (p : pattern) (ty : ty) : pattern =
  let ty = get_inner_type ty in
  (* FIXME: This should be handled somewhere else, ideally in Typing.ml *)
  let recursors = build_recursors ~name transformers in
  let transform_pattern = recursors.recurse_pattern in
  let pat_transformer = transformers.pattern_transformer recursors in
  match pat_transformer p ty with
  | Some p -> p
  | None -> (
      match (p, ty.typ) with
      | (PWild | PVar _), _
      | PBool _, TBool
      | PInt _, TInt _
      | PNode _, TNode
      | PEdge _, TEdge
      | PEdgeId _, TEdge
      | POption None, TOption _ ->
          p
      | POption (Some p), TOption ty -> POption (Some (transform_pattern p ty))
      | PTuple ps, TTuple tys -> PTuple (List.map2 transform_pattern ps tys)
      | PRecord pmap, TRecord tmap ->
          PRecord
            (StringMap.mapi
               (fun l p -> transform_pattern p (StringMap.find l tmap))
               pmap)
      | _, _ ->
          failwith
          @@ Printf.sprintf
               "%s: transform_pattern: pattern %s does not match type %s\n" name
               (Printing.pattern_to_string p)
               (Printing.ty_to_string ty) )

and transform_value ~(name : string) (transformers : transformers) (v : value) :
    value =
  let recursors = build_recursors ~name transformers in
  let transform_ty, transform_value =
    (recursors.recurse_ty, recursors.recurse_value)
  in
  let value_transformer = transformers.value_transformer recursors in
  let v' =
    match value_transformer v with
    | Some v -> v
    | None -> (
        match v.v with
        | VInt _ | VBool _ | VNode _ | VEdge _ | VOption None | VFloat _ -> v
        | VOption (Some v1) -> voption (Some (transform_value v1))
        | VTuple vs -> vtuple (List.map transform_value vs)
        | VRecord map -> vrecord (StringMap.map transform_value map)
        | VTotalMap bdd ->
            let op_key = (e_val v, BatSet.PSet.empty) in
            vmap (BddMap.map op_key (fun v -> transform_value v) bdd) None
        | VClosure _ ->
            failwith @@ name ^ ": transform_value: encountered VClosure" )
  in
  avalue (v', omap transform_ty v.vty, v.vspan)

and transform_exp ~(name : string) (transformers : transformers) (e : exp) : exp
    =
  let recursors = build_recursors ~name transformers in
  let transform_ty, transform_pattern, transform_value, transform_exp =
    ( recursors.recurse_ty,
      recursors.recurse_pattern,
      recursors.recurse_value,
      recursors.recurse_exp )
  in
  let exp_transformer = transformers.exp_transformer recursors in
  let e' =
    match exp_transformer e with
    | Some e -> e
    | None -> (
        match e.e with
        | EVar _ -> e
        | EVal v -> e_val (transform_value v)
        | EOp (op, es) -> eop op (List.map transform_exp es)
        | ESome e -> esome (transform_exp e)
        | ETuple es -> etuple (List.map transform_exp es)
        | ERecord map -> erecord (StringMap.map transform_exp map)
        | EProject (e, l) -> eproject (transform_exp e) l
        | EFun f ->
            efun
              {
                f with
                argty = Some (transform_ty (oget f.argty));
                resty = Some (transform_ty (oget f.resty));
                body = transform_exp f.body;
              }
        | EApp (e1, e2) -> eapp (transform_exp e1) (transform_exp e2)
        | ELet (x, e1, e2) -> elet x (transform_exp e1) (transform_exp e2)
        | EIf (test, e1, e2) ->
            eif (transform_exp test) (transform_exp e1) (transform_exp e2)
        | EMatch (test, branches) ->
            ematch (transform_exp test)
              (mapBranches
                 (fun (p, b) ->
                   (transform_pattern p (oget test.ety), transform_exp b))
                 branches)
        | EBddIf (e1, e2, e3) ->
            ebddIf (transform_exp e1) (transform_exp e2) (transform_exp e3)
        | EToBdd e -> etoBdd (transform_exp e)
        | EToMap e -> etoMap (transform_exp e)
        | EApplyN (e1, es) ->
            eApplyN (transform_exp e1) (List.map transform_exp es) )
  in

  aexp (e', omap transform_ty e.ety, e.espan)

let transform_symbolic ~(name : string) (transformers : transformers) (x, ty, p)
    =
  (x, transform_ty ~name transformers ty, p)

let transform_decl ~(name : string) (transformers : transformers)
    (d : declaration) =
  let transform_ty = transform_ty ~name transformers in
  let transform_exp = transform_exp ~name transformers in
  let transform_symbolic = transform_symbolic ~name transformers in
  match d with
  | DLet (x, e, inline) -> DLet (x, transform_exp e, inline)
  | DInfer (name, e, None) -> DInfer (name, transform_exp e, None)
  | DInfer (name, e, Some c) ->
      DInfer (name, transform_exp e, Some (transform_exp c))
  | DSolve { aty; var_names; init; trans; merge } ->
      let var_names, init, trans, merge =
        ( transform_exp var_names,
          transform_exp init,
          transform_exp trans,
          transform_exp merge )
      in
      DSolve { aty = omap transform_ty aty; var_names; init; trans; merge }
  | DForward
      {
        names_V;
        names_E;
        pty;
        hvty;
        hety;
        fwdInit;
        fwdOut;
        fwdIn;
        hinitV;
        hinitE;
        logE;
        logV;
        bot;
      } ->
      DForward
        {
          pty = omap transform_ty pty;
          hvty = omap transform_ty hvty;
          hety = omap transform_ty hety;
          names_V = transform_exp names_V;
          names_E = transform_exp names_E;
          fwdInit = transform_exp fwdInit;
          fwdOut = transform_exp fwdOut;
          fwdIn = transform_exp fwdIn;
          hinitV = transform_exp hinitV;
          hinitE = transform_exp hinitE;
          logE = transform_exp logE;
          logV = transform_exp logV;
          bot = transform_exp bot;
        }
  | DSymbolic (x, ty, p) ->
      let x, ty, p = transform_symbolic (x, ty, p) in
      let p' = match p with Expr e -> Expr (transform_exp e) | _ -> p in
      DSymbolic (x, ty, p')
  | DUserTy (x, ty) -> DUserTy (x, transform_ty ty)
  | DNodes _ | DEdges _ -> d

let rec map_back_value ~(name : string) (sol : Solution.t)
    (map_back_transformer : map_back_transformer) (v : value) (orig_ty : ty) =
  let map_back_value = map_back_value ~name sol map_back_transformer in
  let map_back_transformer = map_back_transformer map_back_value sol in
  let orig_ty = get_inner_type orig_ty in
  match map_back_transformer v orig_ty with
  | Some v -> v
  | None -> (
      match (v.v, orig_ty.typ) with
      | (VBool _ | VInt _ | VNode _ | VEdge _ | VOption None | VFloat _), _ -> v
      | VOption (Some v'), TOption ty' -> voption (Some (map_back_value v' ty'))
      | VTuple vs, TTuple tys -> vtuple (List.map2 map_back_value vs tys)
      | VRecord vmap, TRecord tmap ->
          vrecord
          @@ StringMap.mapi
               (fun l v -> map_back_value v (StringMap.find l tmap))
               vmap
      | VTotalMap bdd, TMap (_, vty) ->
          (* let op_key = (e_val v, BatSet.PSet.empty) in *)
          vmap
            ( Cudd.Mapleaf.mapleaf1
                (fun v ->
                  map_back_value (Cudd.Mtbddc.get v) vty
                  |> Cudd.Mtbddc.unique BddUtils.tbl_nv)
                (fst bdd),
              snd bdd )
            (* (BddMap.map op_key (fun v -> map_back_value v vty) bdd) *)
            (Some orig_ty)
      | VClosure _, _ ->
          failwith @@ name ^ ": Can't have closures in attributes"
      | VTotalMap (bdd, kty), _ ->
          (* Handling multivalues *)
          let g x =
            map_back_value (Cudd.Mtbddc.get x) orig_ty
            |> Cudd.Mtbddc.unique BddUtils.tbl_nv
          in
          let bdd' = Cudd.Mapleaf.mapleaf1 g bdd in
          vmap (bdd', kty) None
      | (VOption _ | VTuple _ | VRecord _), _ ->
          failwith
          @@ Printf.sprintf
               "%s: map_back_value: value %s does not match type %s" name
               (Printing.value_to_string v)
               (Printing.ty_to_string orig_ty) )

(* NOTE: I don't think solve_tys is necessary or the right way to go here. We
   should store the original type at each transformation pass *)
(* TODO: apply map back to forwarding *)
let map_back_sol ~(name : string) (map_back_transformer : map_back_transformer)
    (solve_tys : ty VarMap.t) (sol : Solution.t) : Solution.t =
  let map_back_value = map_back_value ~name sol map_back_transformer in
  let solves =
    List.map
      (fun (v, { Solution.sol_val }) ->
        let aty = VarMap.find v solve_tys in
        ( v,
          {
            Solution.sol_val =
              AdjGraph.VertexMap.map (fun v -> map_back_value v aty) sol_val;
            attr_ty = aty;
          } ))
      sol.solves
  in
  {
    assertions = sol.assertions;
    (* These transformations shouldn't change the truth value of the assertion *)
    solves;
    forwarding = sol.forwarding;
    nodes = sol.nodes;
  }

let get_solve_types solves =
  let rec add_tys acc e =
    match e.e with
    | EVar x -> (
        match (oget e.ety).typ with
        | TMap (_, vty) -> VarMap.add x vty acc
        | _ -> failwith "Bad DSolve" )
    | _ -> failwith "Bad DSolve"
  in
  List.fold_left (fun acc s -> add_tys acc s.var_names) VarMap.empty solves

let transform_declarations ~(name : string) (ty_transformer : ty transformer)
    (pattern_transformer : pattern_transformer)
    (value_transformer : value transformer) (exp_transformer : exp transformer)
    (map_back_transformer : map_back_transformer) (ds : declarations) =
  let solve_tys = get_solves ds |> get_solve_types in
  let transformers =
    { ty_transformer; pattern_transformer; value_transformer; exp_transformer }
  in
  ( List.map (transform_decl ~name transformers) ds,
    map_back_sol ~name map_back_transformer solve_tys )
