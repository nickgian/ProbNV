(** ** Type inference with efficient generalization via levels;
 * code following http://okmij.org/ftp/ML/generalization.html#levels
*)

open Syntax
open Printing
open ProbNv_datastructures
open ProbNv_utils
open Collections
open Batteries
open Option.Infix

let debug = true

let if_debug s = if debug then print_endline s else ()

let node_ty = TNode

let edge_ty = TEdge

let init_ty aty = concrete (TArrow (concrete node_ty, aty))

let merge_ty aty =
  concrete
    (TArrow
       (concrete node_ty, concrete (TArrow (aty, concrete (TArrow (aty, aty))))))

let trans_ty aty =
  concrete (TArrow (concrete edge_ty, concrete (TArrow (aty, aty))))

(* let solve_ty aty =
   TRecord
    (StringMap.add "init" (init_ty aty)
    @@ StringMap.add "trans" (trans_ty aty)
    @@ StringMap.add "merge" (merge_ty aty)
    @@ StringMap.empty)
   ;; *)

(* Region-like levels for efficient implementation of type generalization *)
let current_level = ref 1

let enter_level () = incr current_level

let leave_level () = decr current_level

let level () = !current_level

let level_reset () = current_level := 1

(* new type variable *)
let fresh_tyvar () = TVar (ref (Unbound (Var.fresh "a", level ())))

(* equality of type variables *)
let equal_tyvars tv1 tv2 = tv1 == tv2

(* physical equality of refs *)

let reset_tyvars () =
  (* name from OCaml's typing/typetext.ml *)
  (*  Var.reset ();  *)
  (* DPW: don't need to do this *)
  level_reset ()

(** * Checking that all expressions and values are typed*)

let rec check_annot_val (v : value) =
  match v.vty with
  | None ->
      Console.error
        (Printf.sprintf "internal type annotation missing: %s\n"
           (Printing.value_to_string v))
  | Some _ -> ()

(* match v.v with
   | VOption (Some v) -> check_annot_val v
   | VTuple vs -> BatList.iter check_annot_val vs
   | VMap map ->
   let bs, _ = BddMap.bindings map in
   BatList.iter
    (fun (v1, v2) ->
      check_annot_val v1;
      check_annot_val v2)
    bs
   | _ -> () *)

let rec check_annot (e : exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ;
     Printf.printf "type: %s\n" (Printing.ty_to_string (oget e.ety)) ; *)
  ( match e.ety with
  | None ->
      Console.error
        (Printf.sprintf "internal type annotation missing: %s\n"
           (Printing.exp_to_string e))
  | Some _ -> () );
  match e.e with
  | EVar _ -> ()
  | EVal v -> check_annot_val v
  | EOp (_, es) -> BatList.iter check_annot es
  | EFun f -> check_annot f.body
  | EApp (e1, e2) ->
      check_annot e1;
      check_annot e2
  | EIf (e1, e2, e3) ->
      check_annot e1;
      check_annot e2;
      check_annot e3
  | ELet (_, e1, e2) ->
      check_annot e1;
      check_annot e2
  | ETuple es -> BatList.iter check_annot es
  | EMatch (e, bs) ->
      check_annot e;
      iterBranches (fun (_, e) -> check_annot e) bs
  | EBddIf (e1, e2, e3) ->
      check_annot e1;
      check_annot e2;
      check_annot e3
  | EToBdd e1 -> check_annot e1
  | EToMap e1 -> check_annot e1
  | EApplyN (e1, e2) ->
      check_annot e1;
      BatList.iter check_annot e2
  | ESome e -> check_annot e
  | EProject (e, _) -> check_annot e
  | ERecord map -> StringMap.iter (fun _ -> check_annot) map

let check_annot_decl (d : declaration) =
  match d with
  | DLet (_, e) | DAssert (e, _) -> check_annot e
  | DSolve { var_names; init; trans; merge; _ } ->
      check_annot var_names;
      check_annot init;
      check_annot trans;
      check_annot merge
  | DUserTy _ | DNodes _ | DEdges _ | DSymbolic _ -> ()

let rec check_annot_decls (ds : declarations) =
  match ds with
  | [] -> ()
  | d :: ds ->
      check_annot_decl d;
      check_annot_decls ds

(** ** Occur Checks, Unification, Generalization*)

(** This code should be shared between HLL and LLL*)

let tyname () = Var.fresh "a"

exception Occurs

(* Execution modes are not required here, we just need to check the base types *)
let occurs tvr (ty : baseTy) : unit =
  let rec occ tvr ty =
    match ty with
    | TVar tvr' when equal_tyvars tvr tvr' -> raise Occurs
    | TVar ({ contents = Unbound (name, l') } as tv) ->
        let min_level =
          match !tvr with Unbound (_, l) -> min l l' | _ -> l'
        in
        tv := Unbound (name, min_level)
    | TVar { contents = Link ty } -> occ tvr ty.typ
    | QVar q ->
        (* this case should not occur, I don't think *)
        if_debug ("qvar " ^ Var.to_string q ^ " appears in occ check");
        ()
    | TArrow (t1, t2) ->
        occ tvr t1.typ;
        occ tvr t2.typ
    | TBool | TInt _ | TNode | TEdge -> ()
    | TTuple ts -> BatList.iter (fun ty -> occ tvr ty.typ) ts
    | TOption t -> occ tvr t.typ
    | TMap (t1, t2) ->
        occ tvr t1.typ;
        occ tvr t2.typ
    | TRecord map -> StringMap.iter (fun _ ty -> occ tvr ty.typ) map
  in

  try occ tvr ty
  with Occurs ->
    Console.error
      (Printf.sprintf "%s occurs in %s\n" (tyvar_to_string !tvr)
         (base_ty_to_string ty))

(* QVar are unexpected: they should've been instantiated *)
(* Modes are also not used here, we just check that the base types can be
   unified. We compute the right mode in the infer_exp/infer_value/infer_decl functions.*)
let rec unify isHLL info e t1 t2 : unit =
  (* similar to unify, but returns a bool indicating if it was successful *)
  let rec try_unifies ts1 ts2 : bool =
    match (ts1, ts2) with
    | [], [] -> true
    | t1 :: ts1, t2 :: ts2 ->
        try_unify t1 t2 t1.mode t2.mode && try_unifies ts1 ts2
    | _, _ -> false
  and try_unify t1 t2 m1 m2 : bool =
    if t1 == t2 then true (* t1 and t2 are physically the same *)
    else
      match (t1.typ, t2.typ) with
      | TVar { contents = Link t1 }, _ -> try_unify t1 t2 m1 m2
      | _, TVar { contents = Link t2 } -> try_unify t1 t2 m1 m2
      | TVar ({ contents = Unbound _ } as tv), t' ->
          if isHLL then (
            occurs tv t';
            tv := Link { t2 with mode = m1 };
            true )
          else
            t1.typ = t2.typ
            ||
            ( occurs tv t';
              tv := Link { t2 with mode = m1 };
              true )
      | t', TVar ({ contents = Unbound _ } as tv) ->
          if isHLL then (
            occurs tv t';
            tv := Link { t1 with mode = m2 };
            true )
          else
            t1.typ = t2.typ
            ||
            ( occurs tv t';
              tv := Link { t1 with mode = m2 };
              true )
      (* | TVar {contents= Link t1}, t2 -> try_unify t1 t2
       * | t1, TVar {contents= Link t2} -> try_unify t1 t2 *)
      | TArrow (tyl1, tyl2), TArrow (tyr1, tyr2) ->
          try_unify tyl1 tyr1 tyl1.mode tyr1.mode
          && try_unify tyl2 tyr2 tyl2.mode tyr2.mode
      | TBool, TBool -> true
      | TInt i, TInt j when i = j -> true
      | TNode, TNode -> true
      | TEdge, TEdge -> true
      | TTuple ts1, TTuple ts2 -> try_unifies ts1 ts2
      | TOption t1, TOption t2 -> try_unify t1 t2 m1 m2
      | TMap (t1, t2), TMap (t3, t4) ->
          try_unify t1 t3 t1.mode t3.mode && try_unify t2 t4 t2.mode t4.mode
      | TRecord map1, TRecord map2 ->
          let open RecordUtils in
          if not (same_labels map1 map2) then false
          else
            BatList.fold_left
              (fun b l ->
                let ty1 = StringMap.find l map1 in
                let ty2 = StringMap.find l map2 in
                b && try_unify ty1 ty2 ty1.mode ty2.mode)
              true (get_record_labels map1)
      | _, _ -> false
  in
  let m1 = t1.mode in
  let m2 = t2.mode in
  if try_unify t1 t2 m1 m2 then ()
  else
    let msg =
      Printf.sprintf "unable to unify types: %s and\n %s" (ty_to_string t1)
        (ty_to_string t2)
    in
    Printf.printf "%s\n" msg;
    Console.error_position info e.espan msg

and unifies isHLL info (e : exp) ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> ()
  | t1 :: ts1, t2 :: ts2 ->
      unify isHLL info e t1 t2;
      unifies isHLL info e ts1 ts2
  | _, _ -> Console.error "wrong number of components in unification"

let unify_opt isHLL info (e : exp) topt1 t2 =
  match topt1 with Some t1 -> unify isHLL info e t1 t2 | None -> ()

let generalize ty =
  let rec gen ty =
    match ty.typ with
    | TVar { contents = Unbound (name, l) } when l > !current_level ->
        { ty with typ = QVar name }
    | TVar { contents = Link ty } -> gen ty
    | TVar _ | TBool | TInt _ | TNode | TEdge -> ty
    | QVar q ->
        if_debug ("qvar " ^ Var.to_string q ^ " appears in generalization check");
        ty
    | TArrow (ty1, ty2) ->
        let ty1 = gen ty1 in
        let ty2 = gen ty2 in
        { ty with typ = TArrow (ty1, ty2) }
    | TTuple ts -> { ty with typ = TTuple (BatList.map (fun ty -> gen ty) ts) }
    | TOption t ->
        let t' = gen t in
        { ty with typ = TOption t' }
    | TMap (ty1, ty2) ->
        let ty1 = gen ty1 in
        let ty2 = gen ty2 in
        { ty with typ = TMap (ty1, ty2) }
    | TRecord map -> { ty with typ = TRecord (StringMap.map gen map) }
  in

  match ty.typ with TArrow _ -> gen ty | _ -> ty

(* instantiation: replace schematic variables with fresh TVar *)
let inst subst ty =
  let rec loop subst ty =
    match ty.typ with
    | QVar name -> (
        try Env.lookup subst name
        with Env.Unbound_var x -> Console.error ("bad instantiation: " ^ x) )
    | TVar { contents = Link ty } -> loop subst ty
    | TVar { contents = Unbound (name, _) } -> (
        if_debug ("found unbound tyvar " ^ Var.to_string name);
        try Env.lookup subst name
        with Env.Unbound_var x -> Console.error ("bad instantiation: " ^ x) )
    | TBool | TInt _ | TNode | TEdge -> ty
    | TArrow (ty1, ty2) ->
        let ty1 = loop subst ty1 in
        let ty2 = loop subst ty2 in
        { ty with typ = TArrow (ty1, ty2) }
    | TTuple ts ->
        let ts = loops subst ts in
        { ty with typ = TTuple ts }
    | TOption t ->
        let t = loop subst t in
        { ty with typ = TOption t }
    | TMap (ty1, ty2) ->
        let ty1 = loop subst ty1 in
        let ty2 = loop subst ty2 in
        { ty with typ = TMap (ty1, ty2) }
    | TRecord map -> { ty with typ = TRecord (StringMap.map (loop subst) map) }
  and loops subst tys =
    match tys with
    | [] -> []
    | ty :: tys ->
        let ty = loop subst ty in
        let tys = loops subst tys in
        ty :: tys
  in
  loop subst ty

let substitute (ty : ty) : ty =
  let map = ref Env.empty in
  let rec substitute_aux ty =
    match ty.typ with
    | QVar name -> (
        match Env.lookup_opt !map name with
        | None ->
            let fty = { typ = fresh_tyvar (); mode = get_mode ty } in
            map := Env.update !map name fty;
            fty
        | Some ty -> ty )
    | TVar _ | TBool | TInt _ | TNode | TEdge -> ty
    | TArrow (ty1, ty2) ->
        { ty with typ = TArrow (substitute_aux ty1, substitute_aux ty2) }
    | TTuple ts ->
        { ty with typ = TTuple (BatList.map (fun ty -> substitute_aux ty) ts) }
    | TOption t -> { ty with typ = TOption (substitute_aux t) }
    | TMap (ty1, ty2) ->
        { ty with typ = TMap (substitute_aux ty1, substitute_aux ty2) }
    | TRecord map ->
        { ty with typ = TRecord (StringMap.map substitute_aux map) }
  in

  substitute_aux ty

(** Return the type of operations *)
let op_typ op =
  match op with
  | And -> ([ concrete TBool; concrete TBool ], concrete TBool)
  | Or -> ([ concrete TBool; concrete TBool ], concrete TBool)
  | Not -> ([ concrete TBool ], concrete TBool)
  (* Integer operators *)
  | UAdd size ->
      ( [ concrete @@ tint_of_size size; concrete @@ tint_of_size size ],
        concrete @@ tint_of_size size )
  (* | USub size -> [tint_of_size size; tint_of_size size], tint_of_size size
     | UAnd size -> [tint_of_size size; tint_of_size size], tint_of_size size *)
  | ULess size ->
      ( [ concrete @@ tint_of_size size; concrete @@ tint_of_size size ],
        concrete TBool )
  | ULeq size ->
      ( [ concrete @@ tint_of_size size; concrete @@ tint_of_size size ],
        concrete TBool )
  | NLess -> ([ concrete TNode; concrete TNode ], concrete TBool)
  | NLeq -> ([ concrete TNode; concrete TNode ], concrete TBool)
  | TGet _ -> failwith "internal error (op_typ): tuple op"
  (* Map operations *)
  | MCreate | MGet | MSet | Eq ->
      failwith
        (Printf.sprintf "(op_typ): %s should be handled elsewhere"
           (Printing.op_to_string op))
  (* LLL expressions *)
  | BddAnd -> ([ symbolic TBool; symbolic TBool ], symbolic TBool)
  | BddOr -> ([ symbolic TBool; symbolic TBool ], symbolic TBool)
  | BddNot -> ([ symbolic TBool ], symbolic TBool)
  | BddAdd n ->
      let t = symbolic @@ tint_of_size n in
      ([ t; t ], t)
  | BddLess n ->
      let t = symbolic @@ tint_of_size n in
      ([ t; t ], symbolic TBool)
  | BddLeq n ->
      let t = symbolic @@ tint_of_size n in
      ([ t; t ], symbolic TBool)
  | BddEq ->
      failwith
        (Printf.sprintf "(op_typ): %s should be handled elsewhere"
           (Printing.op_to_string op))

let texp (e, ty, span) = aexp (e, Some ty, span)

let tvalue (v, ty, span) = avalue (v, Some ty, span)

let canonicalize_type (ty : ty) : ty =
  let rec aux ty map count =
    match ty.typ with
    | TBool | TInt _ | TNode | TEdge -> (ty, map, count)
    | TArrow (t1, t2) ->
        let t1', map, count = aux t1 map count in
        let t2', map, count = aux t2 map count in
        ({ ty with typ = TArrow (t1', t2') }, map, count)
    | TTuple tys ->
        let tys', map, count =
          BatList.fold_left
            (fun (lst, map, count) t ->
              let t', map, count = aux t map count in
              (t' :: lst, map, count))
            ([], map, count) tys
        in
        ({ ty with typ = TTuple (BatList.rev tys') }, map, count)
    | TOption t ->
        let t', map, count = aux t map count in
        ({ ty with typ = TOption t' }, map, count)
    | TMap (t1, t2) ->
        let t1', map, count = aux t1 map count in
        let t2', map, count = aux t2 map count in
        ({ ty with typ = TMap (t1', t2') }, map, count)
    | TRecord tmap ->
        let open RecordUtils in
        let tmap', map, count =
          List.fold_left2
            (fun (tmap, map, count) l t ->
              let t', map, count = aux t map count in
              (StringMap.add l t' tmap, map, count))
            (StringMap.empty, map, count)
            (get_record_labels tmap) (get_record_entries tmap)
        in
        ({ ty with typ = TRecord tmap' }, map, count)
    | QVar tyname -> (
        match VarMap.Exceptionless.find tyname map with
        | None ->
            let new_var = Var.to_var ("a", count) in
            ( { ty with typ = QVar new_var },
              VarMap.add tyname new_var map,
              count + 1 )
        | Some v -> ({ ty with typ = QVar v }, map, count) )
    | TVar r -> (
        match !r with
        | Link t -> aux { t with mode = join_opts t.mode ty.mode } map count
        | Unbound _ -> ({ ty with typ = TBool }, map, count) )
  in
  let result, _, _ = aux ty VarMap.empty 0 in
  result

let textract e =
  match e.ety with
  | None -> failwith "internal error (textract)"
  | Some ty -> (e, ty)

let textractv v =
  match v.vty with
  | None -> failwith "internal error (textractv)"
  | Some ty -> (v, ty)

(** * Type inference for values*)

(** Type infrence for values is common between the two languages*)
let rec infer_value info env record_types (v : Syntax.value) : Syntax.value =
  let ret =
    match v.v with
    | VBool _ -> tvalue (v, concrete TBool, v.vspan)
    | VInt i -> tvalue (v, concrete (tint_of_value i), v.vspan)
    | VNode _ -> tvalue (v, concrete TNode, v.vspan)
    | VEdge _ -> tvalue (v, concrete TEdge, v.vspan)
    | VTuple vs ->
        let vs, ts = infer_values info env record_types vs in
        tvalue (vtuple vs, concrete (TTuple ts), v.vspan)
    | VOption None ->
        let tv = fresh_tyvar () in
        tvalue (voption None, concrete (TOption (concrete tv)), v.vspan)
    | VOption (Some v) ->
        let v, t = textractv (infer_value info env record_types v) in
        let tv = fresh_tyvar () |> concrete in
        unify true info (exp_of_value v) t tv;
        tvalue (voption (Some v), concrete @@ TOption tv, v.vspan)
    | VRecord vmap ->
        (* All VRecords are constructed via ERecords, so shouldn't need
           to check that the record type has been properly declared *)
        let vmap = StringMap.map (infer_value info env record_types) vmap in
        let tmap =
          StringMap.map (fun v -> ProbNv_utils.OCamlUtils.oget v.vty) vmap
        in
        tvalue (vrecord vmap, concrete @@ TRecord tmap, v.vspan)
    | VTotalMap _ | VClosure _ -> failwith "internal error (infer_value)"
  in
  ret

and infer_values info env record_types vs =
  match vs with
  | [] -> ([], [])
  | v :: vs ->
      let v, t = infer_value info env record_types v |> textractv in
      let vs, ts = infer_values info env record_types vs in
      (v :: vs, t :: ts)

(** * Infering Types for Declarations *)

(** Inference for declarations is mostly the same between HLL and LLL. One
    difference is the solution rule, so we reuse most of the code between the
    two expect for DSolve declarations.*)

let rec infer_declarations_aux isHLL infer_exp i info env record_types
    (ds : declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' =
        infer_declaration isHLL infer_exp (i + 1) info env record_types d
      in
      d'
      :: infer_declarations_aux isHLL infer_exp (i + 1) info env' record_types
           ds'

and infer_declaration isHLL infer_exp i info env record_types d :
    ty Env.t * declaration =
  let _infer_exp = infer_exp in
  (* Alias in case we need to modify the usually-static args *)
  let infer_exp = infer_exp (i + 1) info env record_types in
  let open ProbNv_utils.OCamlUtils in
  match d with
  | DLet (x, e1) when isHLL ->
      enter_level ();
      let e1, ty_e1 = infer_exp e1 |> textract in
      (* Printf.printf "Dlet : %s with ty = %s\n" (Var.to_string x)
         (Printing.ty_to_string ty_e1); *)
      leave_level ();
      let ty = generalize ty_e1 in
      (Env.update env x ty, DLet (x, texp (e1, ty, e1.espan)))
  | DLet (x, e1) ->
      let e1, ty_e1 = infer_exp e1 |> textract in
      (Env.update env x ty_e1, DLet (x, texp (e1, ty_e1, e1.espan)))
  | DSymbolic (x, ty, prob) -> (Env.update env x ty, DSymbolic (x, ty, prob))
  | DAssert (e, prob) -> (
      let e' = infer_exp e in
      let ty = oget e'.ety in
      (* Printf.printf "Assertion type: %s" (Printing.ty_to_string ty); *)
      (* Mode should not matter for unification - although it might matter in the TVar case
         but I don't think that case appears here *)
      unify isHLL info e ty { typ = TBool; mode = None };
      (*According to rule Assert we need to check that mode = Multivalue or Concrete *)
      match ty.mode with
      | Some Concrete | Some Multivalue ->
          (Env.update env (Var.create "assert") ty, DAssert (e', prob))
      | None | Some Symbolic ->
          Console.error_position info e.espan "Wrong mode for assertion" )
  | DSolve { aty; var_names; init; trans; merge } -> (
      let init' = infer_exp init in
      let trans' = infer_exp trans in
      let merge' = infer_exp merge in
      let var =
        match var_names.e with
        | EVar x -> x
        | _ -> Console.error_position info init.espan "Bad Solution Declaration"
      in
      let m =
        (* Computing the mode for the solutions according to Solution rule for HLL and LLL *)
        let m1 =
          match (oget init'.ety).typ with
          | TArrow (_, ty2) -> get_mode ty2
          | _ ->
              Console.error_position info init.espan
                "Init must be of function type"
        in
        let mtrans_arg, mtrans_res =
          match (oget trans'.ety).typ with
          | TArrow (_, ty2) -> (
              match ty2.typ with
              | TArrow (tyarg, tyres) -> (get_mode tyarg, get_mode tyres)
              | _ ->
                  Console.error_position info trans.espan
                    "Trans must be of function type" )
          | _ ->
              Console.error_position info trans.espan
                "Trans must be of function type"
        in
        let mmerge_arg1, mmerge_arg2, mmerge_res =
          match (oget merge'.ety).typ with
          | TArrow (_, ty2) -> (
              match ty2.typ with
              | TArrow (tyarg1, ty3) -> (
                  match ty3.typ with
                  | TArrow (tyarg2, tyres) ->
                      (get_mode tyarg1, get_mode tyarg2, get_mode tyres)
                  | _ ->
                      Console.error_position info trans.espan
                        "Merge must be of function type" )
              | _ ->
                  Console.error_position info trans.espan
                    "Merge must be of function type" )
          | _ ->
              Console.error_position info trans.espan
                "Merge must be of function type"
        in
        (*For HLL*)
        if isHLL then
          join (OCamlUtils.oget m1)
            (join (OCamlUtils.oget mtrans_res) (OCamlUtils.oget mmerge_res))
        else if
          (* For LLL *)
          m1 = mtrans_arg && mtrans_arg = mtrans_res && mtrans_res = mmerge_arg1
          && mmerge_arg1 = mmerge_arg2 && mmerge_arg2 = mmerge_res
        then OCamlUtils.oget m1
        else
          Console.error_position info trans.espan
            "Modes of solution declarations do not match"
      in
      let solve_aty =
        match aty with
        | Some ty -> ty
        | None -> { typ = fresh_tyvar (); mode = Some m }
      in
      unify isHLL info init (oget init'.ety) (init_ty solve_aty);
      unify isHLL info trans (oget trans'.ety) (trans_ty solve_aty);
      unify isHLL info merge (oget merge'.ety) (merge_ty solve_aty);

      match m with
      | Symbolic ->
          Console.error_position info trans.espan "Solution cannot be symbolic"
      | _ ->
          let solve_aty = { solve_aty with mode = Some m } in
          let ety =
            { typ = TMap (concrete TNode, solve_aty); mode = Some Concrete }
          in
          ( Env.update env var ety,
            DSolve
              {
                aty = Some solve_aty;
                var_names = aexp (evar var, Some ety, var_names.espan);
                init = init';
                trans = trans';
                merge = merge';
              } ) )
  | DUserTy _ | DNodes _ | DEdges _ -> (env, d)

(** High-Level Language Type Inference *)
module HLLTypeInf = struct
  let unify = unify true

  let unifies = unifies true

  let unify_opt = unify_opt true

  let rec infer_exp i info env record_types (e : exp) : exp =
    let _infer_exp = infer_exp in
    (* Alias in case we need to modify the usually-static args *)
    let infer_exp = infer_exp (i + 1) info env record_types in
    let infer_value = infer_value info env record_types in
    let exp =
      match e.e with
      | EVar x -> (
          match Env.lookup_opt env x with
          | None ->
              Console.error_position info e.espan
                ("unbound variable " ^ Var.to_string x)
          | Some t -> texp (e, substitute t, e.espan) )
      | EVal v ->
          let v, t = infer_value v |> textractv in
          texp (e_val v, t, e.espan)
      | EOp (o, es) -> (
          match (o, es) with
          | Eq, [ e1; e2 ] ->
              let e1, ty1 = infer_exp e1 |> textract in
              let e2, ty2 = infer_exp e2 |> textract in
              unify info e ty1 ty2;
              (*compute the mode, based on the modes of the sub expressions *)
              let m =
                join
                  (OCamlUtils.oget (get_mode ty1))
                  (OCamlUtils.oget (get_mode ty2))
              in
              texp (eop o [ e1; e2 ], mty (Some m) TBool, e.espan)
          | MGet, [ e1; e2 ] -> (
              let e1, mapty = infer_exp e1 |> textract in
              let e2, keyty = infer_exp e2 |> textract in
              let valvar = fresh_tyvar () in
              let keyMode, retMode =
                match (get_inner_type mapty).typ with
                | TMap (kty, vty) -> (get_mode kty, get_mode vty)
                | _ -> failwith "Expected a map type"
              in
              let valty = mty retMode valvar in
              unify info e1 mapty
                { typ = TMap (keyty, valty); mode = get_mode mapty };
              let argMode = get_mode keyty in

              (* check that key mode is concrete *)
              if keyMode = Some Concrete then ()
              else failwith "Non concrete key mode in map";

              match retMode with
              | Some Concrete ->
                  (* Map-Get-C case *)
                  let valMode = join_opts (get_mode mapty) argMode in
                  (* check last premise of rule, i.e. m is C or M *)
                  if valMode = Some Multivalue || valMode = Some Concrete then
                    texp
                      (eop o [ e1; e2 ], { valty with mode = valMode }, e.espan)
                  else failwith "map get cannot return a symbolic"
              | Some Multivalue ->
                  (* Map-Get-M case *)
                  (* check that the argument and the map mode are Concrete *)
                  if argMode = Some Concrete && get_mode mapty = Some Concrete
                  then
                    texp
                      ( eop o [ e1; e2 ],
                        { valty with mode = Some Multivalue },
                        e.espan )
                  else failwith "incompatible modes in map get"
              | _ -> failwith "incompatible mode for map type" )
          | MSet, [ e1; e2; e3 ] ->
              let e1, mapty = infer_exp e1 |> textract in
              let e2, keyty = infer_exp e2 |> textract in
              let e3, valty = infer_exp e3 |> textract in

              let keyMode, retMode =
                match (get_inner_type mapty).typ with
                | TMap (kty, vty) -> (get_mode kty, get_mode vty)
                | _ -> failwith "Expected map type"
              in
              (* Check that the map key and value are in concrete mode *)
              if keyMode = Some Concrete && retMode = Some Concrete then (
                let argKeyMode = get_mode keyty in
                let argValMode = get_mode valty in

                unify info e mapty
                  { typ = TMap (keyty, valty); mode = get_mode mapty };

                match
                  (join_opts keyMode argKeyMode, join_opts retMode argValMode)
                with
                | Some _, Some _ -> (
                    let m = join_opts argKeyMode argValMode in
                    match m with
                    | Some Concrete | Some Multivalue ->
                        texp
                          ( eop o [ e1; e2; e3 ],
                            { mapty with mode = m },
                            e.espan )
                    | _ -> failwith "resulting mode for map set is unsupported"
                    )
                | _ ->
                    failwith
                      "map and map set arguments (key/val) have incompatible \
                       modes" )
              else failwith "Incompatible mode types for map set"
          | MCreate, [ e1 ] ->
              let e1, valty = infer_exp e1 |> textract in
              let keyty = concrete @@ fresh_tyvar () in
              (* Compute resulting map mode *)
              let m = get_mode valty in
              texp
                ( eop o [ e1 ],
                  {
                    typ = TMap (keyty, mty (Some Concrete) valty.typ);
                    mode = m;
                  },
                  e.espan )
          | TGet (idx, _), [ e1 ] -> (
              (* we don't need to do inference here, because this operation
                 is not exposed to the user so type inference will
                 have already happened. *)
              let e1, tty = e1 |> textract in
              match tty.typ with
              | TTuple ts ->
                  texp
                    ( eop o [ e1 ],
                      mty (get_mode tty) (List.nth ts idx).typ,
                      e.espan )
              | _ -> failwith "Expected a tuple type" )
          | _ ->
              let argtys, resty = op_typ o in
              let es, tys = infer_exps (i + 1) info env record_types es in
              unifies info e argtys tys;
              (* See binop rule from paper *)
              let m =
                List.fold_left
                  (fun acc ty -> join (OCamlUtils.oget (get_mode ty)) acc)
                  (OCamlUtils.oget (get_mode (List.hd tys)))
                  (List.tl tys)
              in
              texp (eop o es, mty (Some m) resty.typ, e.espan) )
      | EFun { arg = x; argty; resty; body } ->
          let arg_mode =
            match argty with None -> Some Concrete | Some typ -> get_mode typ
          in
          let ty_x = mty arg_mode (fresh_tyvar ()) in
          (* Printf.printf "x : %s with ty = %s\n" (Var.to_string x)
             (Printing.ty_to_string ty_x); *)
          unify_opt info e argty ty_x;

          let e, ty_e =
            _infer_exp (i + 1) info (Env.update env x ty_x) record_types body
            |> textract
          in
          unify_opt info e resty ty_e;
          (* Printf.printf "after unify:\n";
             Printf.printf "x : %s with ty = %s\n" (Var.to_string x)
               (Printing.ty_to_string ty_x); *)
          (* Functions are always typed as Concrete *)
          texp
            ( efun
                {
                  arg = x;
                  argty = Some ty_x;
                  resty = Some ty_e;
                  body = e;
                  fmode = Some Concrete;
                },
              mty (Some Concrete) (TArrow (ty_x, ty_e)),
              e.espan )
      | EApp (e1, e2) -> (
          (* Based on rules App-C and App-M*)
          (* Type check e1 and e2 *)
          let e1, ty_fun = infer_exp e1 |> textract in
          let e2, ty_arg = infer_exp e2 |> textract in

          let ty_res = fresh_tyvar () in

          (* Printf.printf "ty_fun: %s\n\n" (Printing.ty_to_string ty_fun); *)

          (* Assume concrete mode by default *)
          let ty_fun_mode =
            match (get_inner_type ty_fun).typ with
            | TArrow (_, tyret) -> get_mode tyret
            | _ -> Some Concrete
          in

          unify info e ty_fun
            (mty (Some Concrete) (TArrow (ty_arg, mty ty_fun_mode ty_res)));

          let fun_arg, fun_res =
            match (get_inner_type ty_fun).typ with
            | TArrow (fun_arg, fun_res) -> (fun_arg, fun_res)
            | _ ->
                Console.error_position info e.espan
                  (Printf.sprintf "Function must have arrow type: %s"
                     (Printing.ty_to_string ty_fun))
          in
          (* suppose for now we restricted function arguments to C, i.e. symbolics
             are not allowed, ty_arg should be Concrete or Multivalue
             TODO: allow user to annotate the mode
          *)
          (* check that m1 = Concrete *)
          assert (get_mode fun_arg = Some Concrete);
          (* If m1 is Concrete then m3 is Concrete or multi-value *)
          let _ =
            match get_mode ty_arg with
            | None | Some Symbolic ->
                Console.error_position info e.espan
                  "Argument to application must be in Concrete or Multivalue \
                   mode"
            | _ -> ()
          in

          (* Check the mode of the arrow type *)
          match OCamlUtils.oget (get_mode ty_fun) with
          | Concrete -> (
              (* If rule App-C applies *)
              (* according to App-C, m = m2 U m3 *)
              match
                join_opt
                  (OCamlUtils.oget (get_mode fun_res))
                  (OCamlUtils.oget (get_mode ty_arg))
              with
              | None -> Console.error_position info e.espan "Cannot join modes"
              | Some res_mode ->
                  (* set result mode to m2 U m3 *)
                  texp
                    ( eapp e1 e2,
                      liftTy res_mode (mty (Some res_mode) ty_res),
                      e.espan ) )
          | Multivalue ->
              (* If rule App-M applies *)
              (* modes should not matter for unification *)
              unify info e ty_fun
                (mty (get_mode ty_fun)
                   (TArrow (ty_arg, mty (get_mode fun_res) ty_res)));
              (* Resulting mode is always Multivalue *)
              texp
                ( eapp e1 e2,
                  liftTy Multivalue (mty (Some Multivalue) ty_res),
                  e.espan )
          | Symbolic -> failwith "Impossible case" )
      | EIf (e1, e2, e3) -> (
          (* Based on rules Ite-C, Ite-S, Ite-M *)
          let e1, tcond = infer_exp e1 |> textract in
          let e2, ty2 = infer_exp e2 |> textract in
          let e3, ty3 = infer_exp e3 |> textract in
          (* Unification does not matter for modes *)
          unify info e1 (mty None TBool) tcond;
          unify info e ty2 ty3;

          (* Compute the right mode *)
          match get_mode tcond with
          | None -> Console.error_position info e.espan "No mode computed"
          | Some Concrete -> (
              (* If rule Ite-C applies *)
              match
                get_mode ty2 >>= fun m2 ->
                get_mode ty3 >>= fun m3 -> join_opt m2 m3
              with
              | None -> Console.error_position info e.espan "Join failed"
              | Some m as om ->
                  texp (eif e1 e2 e3, liftTy m (mty om ty2.typ), e.espan) )
          | Some Symbolic -> (
              (* If the guard is typed as Symbolic, it could be Ite-S or Ite-M *)
              match
                get_mode ty2 >>= fun m2 ->
                get_mode ty3 >>= fun m3 -> join_opt m2 m3
              with
              | Some Concrete ->
                  (* if it is concrete then it should depend on the context ite
                     appears in. That means we need to be able to unify modes. For now
                     I am skipping that and assuming Ite-M applies. use a type
                     annotation if you want a symbolic. *)
                  let resty =
                    match e.ety with
                    | None -> Some Multivalue
                    | Some resty -> get_mode resty
                  in
                  texp
                    ( eif e1 e2 e3,
                      liftTy (OCamlUtils.oget resty) (mty resty ty2.typ),
                      e.espan )
              | Some m ->
                  (*otherwise it is Symbolic or Multivalue, i.e. Ite-S or Ite-M*)
                  texp (eif e1 e2 e3, liftTy m (mty (Some m) ty2.typ), e.espan)
              | None -> Console.error_position info e.espan "Join failed" )
          | Some Multivalue ->
              (* Ite-M applies *)
              texp (eif e1 e2 e3, mty (Some Multivalue) ty2.typ, e.espan) )
      | ELet (x, e1, e2) ->
          (* TO DO? Could traverse the term e1 again replacing
             TVars with QVars of the same name. Did not do this for now. *)
          enter_level ();
          let e1, ty_e1 = infer_exp e1 |> textract in
          leave_level ();
          let ty = generalize ty_e1 in
          let e2, ty_e2 =
            _infer_exp (i + 1) info (Env.update env x ty) record_types e2
            |> textract
          in
          texp (elet x e1 e2, ty_e2, e.espan)
      | ETuple es ->
          let es, tys = infer_exps (i + 1) info env record_types es in
          (* mode for tuple is the join of all components *)
          let m =
            List.fold_left
              (fun acc ty1 -> join_opts ty1.mode acc)
              (Some Concrete) tys
          in
          texp (etuple es, { typ = TTuple tys; mode = m }, e.espan)
      | ESome e ->
          (* Like tuple but with one element *)
          let e, t = infer_exp e |> textract in
          texp (esome e, { typ = TOption t; mode = t.mode }, e.espan)
      | EMatch (e1, branches) -> (
          let e1, tmatch = infer_exp e1 |> textract in
          (* Printf.printf "e1: %s, tmatch: %s\n"
             (Printing.exp_to_string e1)
             (Printing.ty_to_string tmatch); *)
          let branches, t =
            infer_branches (i + 1) info env record_types e1 tmatch branches
          in
          match get_mode tmatch with
          | Some Concrete ->
              (* Match-C *)
              texp (ematch e1 branches, t, e1.espan)
          | Some Symbolic -> (
              (*Match-S or Match-M*)
              match get_mode t with
              | Some Concrete ->
                  (* again requires annotation, assuming Multivalue is default behavior *)
                  let resty =
                    match e.ety with
                    | None -> Some Multivalue
                    | Some resty -> get_mode resty
                  in
                  texp (ematch e1 branches, mty resty t.typ, e.espan)
              | Some _ ->
                  (* If it's multivalue or symbolic then that's the mode of the result *)
                  texp (ematch e1 branches, t, e.espan)
              | None ->
                  Console.error_position info e.espan "Join on match failed" )
          | Some Multivalue ->
              (* Match-M applies *)
              texp (ematch e1 branches, mty (Some Multivalue) t.typ, e.espan)
          | None ->
              Console.error_position info e.espan
                "No mode on scrutinee of match expression" )
      | ERecord emap ->
          (* Retrieve the record type corresponding to this expression.
             All record types should be explicitly declared, and
             all labels should appear in exactly one declaration *)
          let open RecordUtils in
          let label = List.hd @@ get_record_labels emap in
          let ferr = Console.error_position info e.espan in
          let tmap = get_type_with_label record_types ferr label in
          if not (same_labels emap tmap) then
            (* The only possible record type was not a match *)
            Console.error_position info e.espan
              "Record does not match any declared record type!";
          let emap = StringMap.map infer_exp emap in
          BatEnum.iter
            (fun l ->
              let e, t1 = StringMap.find l emap |> textract in
              let t2 = StringMap.find l tmap in
              unify info e t1 t2)
            (StringMap.keys emap);
          let m =
            StringMap.fold
              (fun _ e acc -> join_opts (OCamlUtils.oget e.ety).mode acc)
              emap (Some Concrete)
          in
          texp (erecord emap, { typ = TRecord tmap; mode = m }, e.espan)
      | EProject (e1, label) ->
          (* Retrieve the record type containing this label.
             All record types should be explicitly declared, and
             all labels should appear in exactly one declaration *)
          let open RecordUtils in
          let ferr = Console.error_position info e.espan in
          let tmap = get_type_with_label record_types ferr label in
          let label_type = StringMap.find label tmap in
          let e1, ety = infer_exp e1 |> textract in
          unify info e1 ety (mty (get_mode ety) (TRecord tmap));
          texp (eproject e1 label, mty (get_mode ety) label_type.typ, e.espan)
      | EBddIf _ ->
          Console.error_position info e.espan "BddIf should not appear in HLL"
      | EToBdd _ ->
          Console.error_position info e.espan "ToBdd should not appear in HLL"
      | EToMap _ ->
          Console.error_position info e.espan "ToMap should not appear in HLL"
      | EApplyN _ ->
          Console.error_position info e.espan "ApplyN should not appear in HLL"
    in
    (* Printf.printf "infer_exp: %s\n" (Printing.exp_to_string e) ;
       Printf.printf "type: %s\n" (Printing.ty_to_string (oget exp.ety)) ;
       check_annot exp ; *)
    exp

  and infer_exps i info env record_types es =
    match es with
    | [] -> ([], [])
    | e :: es ->
        let e, ty = infer_exp (i + 1) info env record_types e |> textract in
        let es, tys = infer_exps (i + 1) info env record_types es in
        (e :: es, ty :: tys)

  and infer_branches i info env record_types exp tmatch bs =
    match popBranch bs with
    | (p, e), bs when isEmptyBranch bs ->
        let env2 = infer_pattern (i + 1) info env exp tmatch p in
        let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
        (addBranch p e emptyBranch, t)
    | (p, e), bs ->
        let bs, tbranch =
          infer_branches (i + 1) info env record_types exp tmatch bs
        in
        let env2 = infer_pattern (i + 1) info env exp tmatch p in
        let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
        unify info e t tbranch;
        (* Printf.printf "t, tbranch: %s, %s\n" (Printing.ty_to_string t) (Printing.ty_to_string tbranch); *)
        let t = join_ty t tbranch in
        (addBranch p e bs, t)

  (* Modes do not matter for unification so just setting them to concrete *)
  and infer_pattern i info env e tmatch p =
    valid_pat p;
    match p with
    | PWild -> env
    | PVar x -> Env.update env x tmatch
    | PBool _ ->
        unify info e tmatch (concrete TBool);
        env
    | PInt i ->
        unify info e tmatch (concrete (tint_of_value i));
        env
    | PNode _ ->
        unify info e tmatch (concrete TNode);
        env
    | PEdge (p1, p2) ->
        unify info e tmatch (concrete TEdge);
        infer_patterns (i + 1) info env e
          [ concrete TNode; concrete TNode ]
          [ p1; p2 ]
    | PEdgeId _ ->
        unify info e tmatch (concrete TEdge);
        env
    | PTuple ps ->
        let ts = BatList.map (fun _ -> concrete @@ fresh_tyvar ()) ps in
        let ty = concrete (TTuple ts) in
        unify info e tmatch ty;
        infer_patterns (i + 1) info env e ts ps
    | POption x -> (
        let t = concrete @@ fresh_tyvar () in
        unify info e tmatch (concrete @@ TOption t);
        match x with
        | None -> env
        | Some p -> infer_pattern (i + 1) info env e t p )
    | PRecord pmap ->
        let ptmap =
          StringMap.map (fun p -> (p, concrete @@ fresh_tyvar ())) pmap
        in
        let tmap = StringMap.map snd ptmap in
        let ty = concrete @@ TRecord tmap in
        unify info e tmatch ty;
        StringMap.fold
          (fun _ (p, t) env -> infer_pattern (i + 1) info env e t p)
          ptmap env

  and infer_patterns i info env e ts ps =
    match (ts, ps) with
    | [], [] -> env
    | t :: ts, p :: ps ->
        valid_pat p;
        let env = infer_pattern (i + 1) info env e t p in
        infer_patterns (i + 1) info env e ts ps
    | _, _ -> Console.error "bad arity in pattern match"

  (* ensure patterns do not contain duplicate variables *)
  and valid_pat p = valid_pattern Env.empty p |> ignore

  and valid_pattern env p =
    match p with
    | PWild | PBool _ | PInt _ | PNode _ | PEdgeId _ -> env
    | PVar x -> (
        match Env.lookup_opt env x with
        | None -> Env.update env x ()
        | Some _ ->
            Console.error
              ("variable " ^ Var.to_string x ^ " appears twice in pattern") )
    | PEdge (p1, p2) -> valid_patterns env [ p1; p2 ]
    | PTuple ps -> valid_patterns env ps
    | POption None -> env
    | POption (Some p) -> valid_pattern env p
    | PRecord map -> StringMap.fold (fun _ p env -> valid_pattern env p) map env

  and valid_patterns env p =
    match p with
    | [] -> env
    | p :: ps -> valid_patterns (valid_pattern env p) ps

  let infer_declarations info (ds : declarations) : declarations =
    let record_types = get_record_types ds in
    infer_declarations_aux true infer_exp 0 info Env.empty record_types ds
end

(** High-Level Language Type Inference *)
module LLLTypeInf = struct
  let unify = unify false

  let unifies = unifies false

  let unify_opt = unify_opt false

  let rec infer_exp i info env record_types (e : exp) : exp =
    let _infer_exp = infer_exp in
    (* Alias in case we need to modify the usually-static args *)
    let infer_exp = infer_exp (i + 1) info env record_types in
    let exp =
      match e.e with
      | EVar x -> (
          match Env.lookup_opt env x with
          | None ->
              Console.error_position info e.espan
                ("unbound variable " ^ Var.to_string x)
          | Some t -> texp (e, substitute t, e.espan) )
      | EVal _ -> e
      | EOp (o, es) -> (
          match (o, es) with
          | Eq, [ e1; e2 ] ->
              let e1, ty1 = infer_exp e1 |> textract in
              let e2, ty2 = infer_exp e2 |> textract in
              unify info e ty1 ty2;
              (*ensure the modes match*)
              let m1 = OCamlUtils.oget (get_mode ty1) in
              let m2 = OCamlUtils.oget (get_mode ty2) in
              if m1 = m2 then
                texp (eop o [ e1; e2 ], mty (Some m1) TBool, e.espan)
              else
                Console.error_position info e.espan
                  (Printf.sprintf "Mode mismatch in operation: %s and %s"
                     (Printing.mode_to_string m1)
                     (Printing.mode_to_string m2))
          | BddEq, [ e1; e2 ] ->
              let e1, ty1 = infer_exp e1 |> textract in
              let e2, ty2 = infer_exp e2 |> textract in
              unify info e ty1 ty2;
              (*ensure the modes match and are symbolic*)
              let m1 = OCamlUtils.oget (get_mode ty1) in
              let m2 = OCamlUtils.oget (get_mode ty2) in
              if m1 = m2 && m1 = Symbolic then
                texp (eop o [ e1; e2 ], mty (Some m1) TBool, e.espan)
              else
                Console.error_position info e.espan
                  (Printf.sprintf "Mode mismatch in operation: %s and %s"
                     (Printing.mode_to_string m1)
                     (Printing.mode_to_string m2))
          | MGet, [ e1; e2 ] -> (
              let _, mapty = e1 |> textract in
              let _, keyty = e2 |> textract in
              let kty, vty =
                match (get_inner_type mapty).typ with
                | TMap (kty, vty) -> (kty, vty)
                | _ -> failwith "Expected a map type"
              in

              (* Check that the key type matches *)
              unify info e2 kty keyty;
              (* Check that the return type matches *)
              unify info e (OCamlUtils.oget e.ety) vty;

              let argMode = get_mode keyty in

              (* check that key and arg mode is concrete *)
              if get_mode kty = Some Concrete && argMode = Some Concrete then ()
              else failwith "Non concrete key mode in map";

              match get_mode vty with
              | Some Concrete ->
                  (* Map-Get-C case *)
                  let valMode = get_mode mapty in
                  (* check that the map is in Concrete mode, i.e. m is C *)
                  if valMode = Some Concrete then
                    texp
                      ( eop o [ e1; e2 ],
                        { vty with mode = Some Concrete },
                        e.espan )
                  else
                    failwith
                      "LLL: map-get-c cannot return a symbolic or multivalue"
              | Some Multivalue ->
                  (* Map-Get-M case *)
                  (* check that the map mode is Concrete *)
                  if get_mode mapty = Some Concrete then
                    texp
                      ( eop o [ e1; e2 ],
                        { vty with mode = Some Multivalue },
                        e.espan )
                  else failwith "incompatible modes in map get"
              | _ -> failwith "incompatible mode for map type" )
          | MSet, [ e1; e2; e3 ] ->
              let _, mapty = e1 |> textract in
              let _, keyty = e2 |> textract in
              let _, valty = e3 |> textract in

              let keyMode, retMode =
                match (get_inner_type mapty).typ with
                | TMap (kty, vty) -> (get_mode kty, get_mode vty)
                | _ -> failwith "Expected map type"
              in
              (* Check that the map key and value are in concrete mode *)
              if
                keyMode = Some Concrete && retMode = Some Concrete
                && get_mode mapty = Some Concrete
              then (
                unify info e mapty
                  { typ = TMap (keyty, valty); mode = get_mode mapty };

                let argKeyMode = get_mode keyty in
                let argValMode = get_mode valty in
                if argKeyMode = Some Concrete && argValMode = Some Concrete then
                  texp
                    ( eop o [ e1; e2; e3 ],
                      { mapty with mode = Some Concrete },
                      e.espan )
                else failwith "LLL: Map key and value set must be concrete." )
              else failwith "LLL: Map set, map must be concrete."
          | MCreate, [ e1 ] -> (
              let _, valty = e1 |> textract in
              match OCamlUtils.oget e.ety with
              | { typ = TMap (kty, vty); mode = _ } as mapty ->
                  unify info e vty valty;
                  if
                    get_mode mapty = Some Concrete
                    && get_mode vty = Some Concrete
                    && get_mode valty = Some Concrete
                  then
                    texp
                      ( eop o [ e1 ],
                        { typ = TMap (kty, valty); mode = Some Concrete },
                        e.espan )
                  else failwith "Mode mismatch in MCreate"
              | _ -> failwith "Type mismatch in MCreate" )
          | TGet (idx, _), [ e1 ] -> (
              (* we don't need to do inference here, because this operation
                  is not exposed to the user so type inference will
                  have already happened. *)
              let e1, tty = e1 |> textract in
              match tty.typ with
              | TTuple ts ->
                  texp
                    ( eop o [ e1 ],
                      mty (get_mode tty) (List.nth ts idx).typ,
                      e.espan )
              | _ -> failwith "Expected a tuple type" )
          | _ ->
              let argtys, resty = op_typ o in
              let es, tys = infer_exps (i + 1) info env record_types es in
              unifies info e argtys tys;
              (* See binop rule from paper *)
              let m1 = get_mode (List.hd tys) in
              if
                List.for_all
                  (fun ty -> OCamlUtils.oget (get_mode ty) = OCamlUtils.oget m1)
                  (List.tl tys)
              then texp (eop o es, mty m1 resty.typ, e.espan)
              else
                Console.error_position info e.espan "Mode mismatch in operation"
          )
      | EFun { arg = x; argty; resty; body } ->
          let arg_mode =
            match argty with None -> Some Concrete | Some typ -> typ.mode
          in
          let e, ty_e =
            textract body
            (* _infer_exp (i + 1) info
                 (Env.update env x (OCamlUtils.oget argty))
                 record_types body
               |> textract *)
          in
          unify_opt info e resty ty_e;
          (* Functions are always typed as Concrete *)
          texp
            ( efun
                {
                  arg = x;
                  argty;
                  resty = Some ty_e;
                  body = e;
                  fmode = Some Concrete;
                },
              mty (Some Concrete) (TArrow (OCamlUtils.oget argty, ty_e)),
              e.espan )
      | EApp (e1, e2) ->
          (* Based on rules App-C and App-M*)
          (* Type check e1 and e2 *)
          let e1, ty_fun = e1 |> textract in
          let e2, ty_arg = e2 |> textract in
          let fun_arg, fun_res =
            match (get_inner_type ty_fun).typ with
            | TArrow (fun_arg, fun_res) -> (fun_arg, fun_res)
            | _ ->
                Console.error_position info e.espan
                  "Function must have arrow type"
          in
          (* suppose for now we restricted function arguments to C, i.e. symbolics
             are not allowed, ty_arg should be Concrete or Multivalue
             TODO: allow user to annotate the mode
          *)
          (* check that m1 = m3 *)
          if get_mode fun_arg = get_mode ty_arg then (
            let ty_res = fresh_tyvar () in
            (* modes should not matter for unification *)
            unify info e ty_fun (mty None (TArrow (ty_arg, mty None ty_res)));
            (* set result mode to m2 mode *)
            texp (eapp e1 e2, mty (get_mode fun_res) ty_res, e.espan) )
          else
            Console.error_position info e.espan
              "Function argument mode must match with the mode of the \
               expression applied"
      | EIf (e1, e2, e3) -> (
          (* Based on rules Ite of the LLL*)
          let e1, tcond = e1 |> textract in
          let e2, ty2 = e2 |> textract in
          let e3, ty3 = e3 |> textract in

          unify info e1 (mty (Some Concrete) TBool) tcond;
          unify info e ty2 ty3;

          (* if not (Syntax.equal_tys ty2 ty3) then (
             Printf.printf "true branch: %s\n" (Printing.ty_to_string ty2);
             Printf.printf "false branch: %s\n" (Printing.ty_to_string ty3);
             failwith "If-Then-Else branch types do not match" ); *)

          (* Check the mode *)
          match get_mode tcond with
          | None -> Console.error_position info e.espan "No mode computed"
          | Some Concrete -> (
              (* If rule Ite applies *)
              match (get_mode ty2, get_mode ty3) with
              | (Some m2, Some m3) as m when m2 = m3 ->
                  texp (eif e1 e2 e3, mty (fst m) ty2.typ, e.espan)
              | Some m2, Some m3 ->
                  Console.error_position info e.espan
                    (Printf.sprintf "Mode mismatch between %s and %s"
                       (Printing.mode_to_string m2)
                       (Printing.mode_to_string m3))
              | _, _ -> Console.error_position info e.espan "Missing mode" )
          | Some _ ->
              Console.error_position info e.espan
                "Symbolic/Multivalue guard - mistyped mode in Ite" )
      | ELet (x, e1, e2) ->
          let e2, ty_e2 = e2 |> textract in
          texp (elet x e1 e2, ty_e2, e.espan)
      | ETuple es ->
          let es, tys = infer_exps (i + 1) info env record_types es in
          let m = get_mode (OCamlUtils.oget e.ety) in
          if List.for_all (fun ty2 -> get_mode ty2 = m) (List.tl tys) then
            texp (etuple es, { typ = TTuple tys; mode = m }, e.espan)
          else Console.error_position info e.espan "Mode mismatch in tuple"
      | ESome e ->
          let e, t = infer_exp e |> textract in
          texp (esome e, { typ = TOption t; mode = get_mode t }, e.espan)
      | EMatch (e1, branches) -> (
          let e1, tmatch = infer_exp e1 |> textract in
          let branches, t =
            infer_branches (i + 1) info env record_types e1 tmatch branches
          in
          (* Check the mode of the scrutinee *)
          match get_mode tmatch with
          | None -> Console.error_position info e.espan "No mode computed"
          | Some Concrete ->
              (* If rule Match applies *)
              texp (ematch e1 branches, t, e1.espan)
          | Some _ ->
              (* Printf.printf "tmatch: %s\n" (Printing.ty_to_string tmatch);
                 Printf.printf "Match: %s\n"
                   (Printing.exp_to_string ~show_types:true e); *)
              Console.error_position info e.espan
                "Symbolic/Multivalue guard - mistyped mode in Match" )
      | ERecord emap ->
          (* Retrieve the record type corresponding to this expression.
             All record types should be explicitly declared, and
             all labels should appear in exactly one declaration *)
          let open RecordUtils in
          let label = List.hd @@ get_record_labels emap in
          let ferr = Console.error_position info e.espan in
          let tmap = get_type_with_label record_types ferr label in
          if not (same_labels emap tmap) then
            (* The only possible record type was not a match *)
            Console.error_position info e.espan
              "Record does not match any declared record type!";
          (* let emap = StringMap.map (fun e -> OCamlUtils.oget e.ety) emap in *)
          let m = get_mode (OCamlUtils.oget e.ety) in
          BatEnum.iter
            (fun l ->
              let e1, t1 = StringMap.find l emap |> textract in
              let t2 = StringMap.find l tmap in
              unify info e1 t1 t2)
            (StringMap.keys emap);
          if
            StringMap.for_all
              (fun _ e -> get_mode (OCamlUtils.oget e.ety) = m)
              emap
          then texp (erecord emap, { typ = TRecord tmap; mode = m }, e.espan)
          else Console.error_position info e.espan "Record mismatch in tuple"
      | EProject (e1, label) ->
          (* Retrieve the record type containing this label.
             All record types should be explicitly declared, and
             all labels should appear in exactly one declaration *)
          let open RecordUtils in
          let ferr = Console.error_position info e.espan in
          let tmap = get_type_with_label record_types ferr label in
          let label_type = StringMap.find label tmap in
          let e1, ety = e1 |> textract in
          unify info e1 ety (mty (get_mode ety) (TRecord tmap));
          texp (eproject e1 label, mty (get_mode ety) label_type.typ, e.espan)
      | EBddIf (e1, e2, e3) -> (
          (* Based on rule Ite of the LLL*)
          let e1, tcond = infer_exp e1 |> textract in
          let e2, ty2 = infer_exp e2 |> textract in
          let e3, ty3 = infer_exp e3 |> textract in
          (* Unification does not matter for modes *)
          unify info e1 (mty None TBool) tcond;
          unify info e ty2 ty3;

          (* Check the mode *)
          match get_mode tcond with
          | None -> Console.error_position info e.espan "No mode computed"
          | Some Symbolic -> (
              (* If rule Ite applies *)
              match (get_mode ty2, get_mode ty3) with
              | Some Symbolic, Some Symbolic ->
                  texp (ebddIf e1 e2 e3, mty (Some Symbolic) ty2.typ, e.espan)
              | _ -> Console.error_position info e.espan "Mode mismatch" )
          | _ ->
              Console.error_position info e.espan
                "Concrete/Multivalue guard - mistyped mode in Ite-S" )
      | EToBdd e1 -> (
          (* Based on rule ToBdd of LLL*)
          (* Printf.printf "toBdd before infer: %s\n"
             (Printing.exp_to_string ~show_types:true e1); *)
          let e1, ty1 = infer_exp e1 |> textract in
          (* Printf.printf "toBdd: %s\n"
             (Printing.exp_to_string ~show_types:true e1); *)
          match get_mode ty1 with
          | Some Concrete -> etoBdd e1
          | _ ->
              Console.error_position info e.espan
                "ToBdd applied to non concrete expression" )
      | EToMap e1 -> (
          (* Based on rule ToMap of LLL*)
          (* Printf.printf "ETomap: %s\n"
             (Printing.ty_to_string (OCamlUtils.oget e1.ety)); *)
          let e1, ty1 = e1 |> textract in
          (* Printf.printf "ETomap: %s\n" (Printing.ty_to_string ty1); *)
          match get_mode ty1 with
          | Some Concrete -> texp (etoMap e1, liftMultiTy ty1, e.espan)
          | _ ->
              Console.error_position info e.espan
                "ToBdd applied to non concrete expression" )
      | EApplyN (e1, es) ->
          (* Based on rule ApplyN of LLL *)
          let e1, ty1 = infer_exp e1 |> textract in
          let es, tys = infer_exps (i + 1) info env record_types es in

          (* get the types of the function e1*)
          let rec func_tys ty acc =
            match ty.typ with
            | TArrow (t1, t2) -> func_tys t2 (t1 :: acc)
            | TVar { contents = Link t } -> func_tys t acc
            | _ -> ty :: acc
          in

          let resty, ftys =
            match func_tys ty1 [] with
            | resty :: ftys -> (resty, List.rev ftys)
            | _ -> failwith "expected a list with at least one element"
          in

          (* Make sure the types match and the modes are correct according to the rule of applyN *)
          let () =
            List.iter2
              (fun fty ty ->
                if
                  OCamlUtils.oget fty.mode = Concrete
                  && (ty.mode = Some Multivalue || ty.mode = Some Symbolic)
                then unify info e fty ty
                else
                  Console.error_position info e.espan
                    "ApplyN modes do not match")
              ftys tys
          in
          texp (eApplyN e1 es, mty (Some Multivalue) resty.typ, e.espan)
    in
    (* Printf.printf "infer_exp: %s\n" (Printing.exp_to_string e) ;
       Printf.printf "type: %s\n" (Printing.ty_to_string (oget exp.ety)) ;
       check_annot exp ; *)
    exp

  and infer_exps i info env record_types es =
    match es with
    | [] -> ([], [])
    | e :: es ->
        let e, ty = infer_exp (i + 1) info env record_types e |> textract in
        let es, tys = infer_exps (i + 1) info env record_types es in
        (e :: es, ty :: tys)

  and infer_branches i info env record_types exp tmatch bs =
    match popBranch bs with
    | (p, e), bs when isEmptyBranch bs ->
        let env2 = infer_pattern (i + 1) info env exp tmatch p in
        let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
        (addBranch p e emptyBranch, t)
    | (p, e), bs ->
        let bs, tbranch =
          infer_branches (i + 1) info env record_types exp tmatch bs
        in
        let env2 = infer_pattern (i + 1) info env exp tmatch p in
        let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
        unify info e t tbranch;
        (* Check that mode of tbranch matches mode of t*)
        if get_mode t = get_mode tbranch then (addBranch p e bs, t)
        else
          Console.error_position info e.espan
            "Mode mismatch in match expression"

  and infer_pattern i info env e tmatch p =
    valid_pat p;
    match p with
    | PWild -> env
    | PVar x -> Env.update env x tmatch
    | PBool _ ->
        unify info e tmatch (concrete TBool);
        env
    | PInt i ->
        unify info e tmatch (concrete (tint_of_value i));
        env
    | PNode _ ->
        unify info e tmatch (concrete TNode);
        env
    | PEdge (p1, p2) ->
        unify info e tmatch (concrete TEdge);
        infer_patterns (i + 1) info env e
          [ concrete TNode; concrete TNode ]
          [ p1; p2 ]
    | PEdgeId _ ->
        unify info e tmatch (concrete TEdge);
        env
    | PTuple ps ->
        let ts = BatList.map (fun _ -> concrete @@ fresh_tyvar ()) ps in
        let ty = concrete (TTuple ts) in
        unify info e tmatch ty;
        infer_patterns (i + 1) info env e ts ps
    | POption x -> (
        let t = concrete @@ fresh_tyvar () in
        unify info e tmatch (concrete @@ TOption t);
        match x with
        | None -> env
        | Some p -> infer_pattern (i + 1) info env e t p )
    | PRecord pmap ->
        let ptmap =
          StringMap.map (fun p -> (p, concrete @@ fresh_tyvar ())) pmap
        in
        let tmap = StringMap.map snd ptmap in
        let ty = concrete @@ TRecord tmap in
        unify info e tmatch ty;
        StringMap.fold
          (fun _ (p, t) env -> infer_pattern (i + 1) info env e t p)
          ptmap env

  and infer_patterns i info env e ts ps =
    match (ts, ps) with
    | [], [] -> env
    | t :: ts, p :: ps ->
        valid_pat p;
        let env = infer_pattern (i + 1) info env e t p in
        infer_patterns (i + 1) info env e ts ps
    | _, _ -> Console.error "bad arity in pattern match"

  (* ensure patterns do not contain duplicate variables *)
  and valid_pat p = valid_pattern Env.empty p |> ignore

  and valid_pattern env p =
    match p with
    | PWild | PBool _ | PInt _ | PNode _ | PEdgeId _ -> env
    | PVar x -> (
        match Env.lookup_opt env x with
        | None -> Env.update env x ()
        | Some _ ->
            Console.error
              ("variable " ^ Var.to_string x ^ " appears twice in pattern") )
    | PEdge (p1, p2) -> valid_patterns env [ p1; p2 ]
    | PTuple ps -> valid_patterns env ps
    | POption None -> env
    | POption (Some p) -> valid_pattern env p
    | PRecord map -> StringMap.fold (fun _ p env -> valid_pattern env p) map env

  and valid_patterns env p =
    match p with
    | [] -> env
    | p :: ps -> valid_patterns (valid_pattern env p) ps

  let infer_declarations info (ds : declarations) : declarations =
    let record_types = get_record_types ds in
    infer_declarations_aux false infer_exp 0 info Env.empty record_types ds
end

let rec equiv_tys ty1 ty2 =
  equal_tys (canonicalize_type ty1) (canonicalize_type ty2)
