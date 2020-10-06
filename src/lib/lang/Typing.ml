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

(* | ETuple es -> BatList.iter check_annot es
   | ESome e -> check_annot e
   | EMatch (e, bs) ->
   check_annot e;
   iterBranches (fun (_, e) -> check_annot e) bs
   | ETy (e, _) | EProject (e, _) -> check_annot e
   | ERecord map -> StringMap.iter (fun _ -> check_annot) map *)

let check_annot_decl (d : declaration) =
  match d with
  | DLet (_, e) | DAssert e -> check_annot e
  | DSolve { var_names; init; trans; merge; _ } ->
      check_annot var_names;
      check_annot init;
      check_annot trans;
      check_annot merge
  (* | DUserTy _  *)
  | DNodes _ | DEdges _ | DSymbolic _ -> ()

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
    (* | TRecord map -> StringMap.iter (fun _ -> occ tvr) map
       | TTuple ts -> BatList.iter (occ tvr) ts
       | TOption t -> occ tvr t
       | TMap (t1, t2) ->
       occ tvr t1;
       occ tvr t2 *)
  in
  try occ tvr ty
  with Occurs ->
    Console.error
      (Printf.sprintf "%s occurs in %s\n" (tyvar_to_string !tvr)
         (base_ty_to_string ty))

(* QVar are unexpected: they should've been instantiated *)
(* Modes are also not used here, we just check that the base types can be
   unified. We compute the right mode in the infer_exp/infer_value/infer_decl functions.*)
let rec unify info e t1 t2 : unit =
  (* similar to unify, but returns a bool indicating if it was successful *)
  let rec try_unifies ts1 ts2 : bool =
    match (ts1, ts2) with
    | [], [] -> true
    | t1 :: ts1, t2 :: ts2 -> try_unify t1 t2 && try_unifies ts1 ts2
    | _, _ -> false
  and try_unify t1 t2 : bool =
    if t1 == t2 then true (* t1 and t2 are physically the same *)
    else
      match (t1.typ, t2.typ) with
      | TVar { contents = Link t1 }, _ -> try_unify t1 t2
      | _, TVar { contents = Link t2 } -> try_unify t1 t2
      | TVar ({ contents = Unbound _ } as tv), t' ->
          occurs tv t';
          tv := Link t2;
          true
      | t', TVar ({ contents = Unbound _ } as tv) ->
          occurs tv t';
          tv := Link t1;
          true
      (* | TVar {contents= Link t1}, t2 -> try_unify t1 t2
       * | t1, TVar {contents= Link t2} -> try_unify t1 t2 *)
      | TArrow (tyl1, tyl2), TArrow (tyr1, tyr2) ->
          try_unify tyl1 tyr1 && try_unify tyl2 tyr2
      | TBool, TBool -> true
      | TInt i, TInt j when i = j -> true
      | TNode, TNode -> true
      | TEdge, TEdge -> true
      (* | TTuple ts1, TTuple ts2 -> try_unifies ts1 ts2
         | TOption t1, TOption t2 -> try_unify t1 t2
         | TMap (t1, t2), TMap (t3, t4) -> try_unify t1 t3 && try_unify t2 t4
         | TRecord map1, TRecord map2 ->
         let open RecordUtils in
         if not (same_labels map1 map2)
         then false
         else
          BatList.fold_left
            (fun b l -> b && try_unify (StringMap.find l map1) (StringMap.find l map2))
            true
            (get_record_labels map1) *)
      | _, _ -> false
  in
  if try_unify t1 t2 then ()
  else
    let msg =
      Printf.sprintf "unable to unify types: %s and\n %s" (ty_to_string t1)
        (ty_to_string t2)
    in
    Printf.printf "%s\n" msg;
    Console.error_position info e.espan msg

and unifies info (e : exp) ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> ()
  | t1 :: ts1, t2 :: ts2 ->
      unify info e t1 t2;
      unifies info e ts1 ts2
  | _, _ -> Console.error "wrong number of components in unification"

let unify_opt info (e : exp) topt1 t2 =
  match topt1 with Some t1 -> unify info e t1 t2 | None -> ()

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
    (* | TRecord map -> TRecord (StringMap.map gen map)
       | TTuple ts -> TTuple (BatList.map gen ts)
       | TOption t ->
       let ty = gen t in
       TOption ty
       | TMap (ty1, ty2) ->
       let ty1 = gen ty1 in
       let ty2 = gen ty2 in
       TMap (ty1, ty2) *)
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
  (* | TTuple ts ->
     let ts = loops subst ts in
     TTuple ts
     | TRecord map -> TRecord (StringMap.map (loop subst) map)
     | TOption t ->
     let t = loop subst t in
     TOption t
     | TMap (ty1, ty2) ->
     let ty1 = loop subst ty1 in
     let ty2 = loop subst ty2 in
     TMap (ty1, ty2) *)
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
    (* | TRecord map -> TRecord (StringMap.map substitute_aux map)
       | TTuple ts -> TTuple (BatList.map substitute_aux ts)
       | TOption t -> TOption (substitute_aux t)
       | TMap (ty1, ty2) -> TMap (substitute_aux ty1, substitute_aux ty2) *)
  in
  substitute_aux ty

(** Return the type of operations *)
let op_typ op =
  match op with
  | And -> ([ concrete TBool; concrete TBool ], concrete TBool)
  (* | Or -> [TBool; TBool], TBool *)
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
  (* | ULeq size -> [tint_of_size size; tint_of_size size], TBool
     | NLess -> [TNode; TNode], TBool
     | NLeq -> [TNode; TNode], TBool *)
  (* | TGet _ | TSet _ -> failwith "internal error (op_typ): tuple op" *)
  (* Map operations *)
  (* | MCreate
     | MGet
     | MSet
     | MMap
     | MMerge
     | MMapFilter
     | MMapIte
     | MFoldNode
     | MFoldEdge
     | MForAll *)
  | Eq ->
      failwith
        (Printf.sprintf "(op_typ): %s should be handled elsewhere"
           (Printing.op_to_string op))
  (* LLL expressions *)
  | BddAnd -> ([ symbolic TBool; symbolic TBool ], symbolic TBool)
  | BddNot -> ([ symbolic TBool ], symbolic TBool)
  | BddAdd ->
      (* The size of the integers do not matter here, but only for the
         surface language, so setting it to 0 to avoid changing the type of TInt to an option.*)
      let t = symbolic @@ tint_of_size 0 in
      ([ t; t ], t)
  | BddLess ->
      let t = symbolic @@ tint_of_size 0 in
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
    (* | TTuple tys ->
       let tys', map, count =
        BatList.fold_left
          (fun (lst, map, count) t ->
            let t', map, count = aux t map count in
            t' :: lst, map, count)
          ([], map, count)
          tys
       in
       TTuple (BatList.rev tys'), map, count
       | TRecord tmap ->
       let open RecordUtils in
       let tmap', map, count =
        List.fold_left2
          (fun (tmap, map, count) l t ->
            let t', map, count = aux t map count in
            StringMap.add l t' tmap, map, count)
          (StringMap.empty, map, count)
          (get_record_labels tmap)
          (get_record_entries tmap)
       in
       TRecord tmap', map, count
       | TOption t ->
       let t', map, count = aux t map count in
       TOption t', map, count
       | TMap (t1, t2) ->
       let t1', map, count = aux t1 map count in
       let t2', map, count = aux t2 map count in
       TMap (t1', t2'), map, count *)
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
    (* | VMap m ->
       let vs, default = BddMap.bindings m in
       let default, dty = infer_value default |> textractv in
       (match vs with
       | [] ->
        (* let ty = fresh_tyvar () in *)
        let ty = fresh_tyvar () in
        tvalue (vmap m, TMap (ty, dty), v.vspan)
       (* (match v.vty with *)
       (*  | None -> *)
       (*     let ty = fresh_tyvar () in *)
       (*     tvalue (vmap m, TMap (ty, dty), v.vspan) *)
       (*  | Some ty -> *)
       (*     let map = BddMap.create ~key_ty:ty default in *)
       (*     tvalue (vmap map, TMap (ty, dty), v.vspan)) *)
       | (kv, vv) :: _ ->
        let _, kvty = infer_value kv |> textractv in
        let _, vvty = infer_value vv |> textractv in
        unify info (exp_of_value v) vvty dty;
        let vs =
          BatList.map
            (fun (kv2, vv2) ->
              let kv2, kvty2 = infer_value kv2 |> textractv in
              let vv2, vvty2 = infer_value vv2 |> textractv in
              unify info (exp_of_value v) kvty kvty2;
              unify info (exp_of_value v) vvty vvty2;
              kv2, vv2)
            vs
        in
        let map = BddMap.from_bindings ~key_ty:kvty (vs, default) in
        tvalue (vmap map, TMap (kvty, vvty), v.vspan))
       | VTuple vs ->
       let vs, ts = infer_values info env record_types vs in
       tvalue (vtuple vs, TTuple ts, v.vspan)
       | VRecord vmap ->
       (* All VRecords are constructed via ERecords, so shouldn't need
         to check that the record type has been properly declared *)
       let vmap = StringMap.map infer_value vmap in
       let tmap = StringMap.map (fun v -> Nv_utils.OCamlUtils.oget v.vty) vmap in
       tvalue (vrecord vmap, TRecord tmap, v.vspan)
       | VOption None ->
       let tv = fresh_tyvar () in
       tvalue (voption None, TOption tv, v.vspan)
       | VOption (Some v) ->
       let v, t = infer_value v |> textractv in
       let tv = fresh_tyvar () in
       unify info (exp_of_value v) t tv;
       tvalue (voption (Some v), TOption tv, v.vspan) *)
    | VClosure _ -> failwith "internal error (infer_value)"
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
  | DLet (x, e1) ->
      enter_level ();
      let e1, ty_e1 = infer_exp e1 |> textract in
      leave_level ();
      let ty = generalize ty_e1 in
      (Env.update env x ty, DLet (x, texp (e1, ty, e1.espan)))
  | DSymbolic (x, ty) -> (Env.update env x ty, DSymbolic (x, ty))
  | DAssert e -> (
      let e' = infer_exp e in
      let ty = oget e'.ety in
      (* Mode should not matter for unification - although it might matter in the TVar case
         but I don't think that case appears here *)
      unify info e ty { typ = TBool; mode = None };
      (*According to rule Assert we need to check that mode = Multivalue or Concrete *)
      match ty.mode with
      | Some Concrete | Some Multivalue ->
          (Env.update env (Var.create "assert") ty, DAssert e')
      | None | Some Symbolic ->
          Console.error_position info e.espan "Wrong mode for assertion" )
  | DSolve { aty; var_names; init; trans; merge } -> (
      let solve_aty =
        match aty with
        | Some ty -> ty
        | None -> { typ = fresh_tyvar (); mode = None }
      in
      let init' = infer_exp init in
      let trans' = infer_exp trans in
      let merge' = infer_exp merge in
      unify info init (oget init'.ety) (init_ty solve_aty);
      unify info trans (oget trans'.ety) (trans_ty solve_aty);
      unify info merge (oget merge'.ety) (merge_ty solve_aty);
      let var =
        match var_names.e with
        | EVar x -> x
        | _ -> Console.error_position info init.espan "Bad Solution Declaration"
      in
      let m =
        (* Computing the mode for the solutions according to Solution rule for HLL and LLL *)
        let m1 =
          match (oget init'.ety).typ with
          | TArrow (_, ty2) -> ty2.mode
          | _ ->
              Console.error_position info init.espan
                "Init must be of function type"
        in
        let mtrans_arg, mtrans_res =
          match (oget trans'.ety).typ with
          | TArrow (_, ty2) -> (
              match ty2.typ with
              | TArrow (tyarg, tyres) -> (tyarg.mode, tyres.mode)
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
                      (tyarg1.mode, tyarg2.mode, tyres.mode)
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
        if isHLL then
          join (OCamlUtils.oget m1)
            (join (OCamlUtils.oget mtrans_res) (OCamlUtils.oget mmerge_res))
        else if
          m1 = mtrans_arg && mtrans_arg = mtrans_res && mtrans_res = mmerge_arg1
          && mmerge_arg1 = mmerge_arg2 && mmerge_arg2 = mmerge_res
        then OCamlUtils.oget m1
        else
          Console.error_position info trans.espan
            "Modes of solution declarations do not match"
      in
      match m with
      | Symbolic ->
          Console.error_position info trans.espan "Solution cannot be symbolic"
      | _ ->
          (* we don't have maps so I will do it as a function *)
          (* let ety = TMap (TNode, solve_aty) in *)
          let solve_aty = { solve_aty with mode = Some m } in
          let ety =
            { typ = TArrow (concrete TNode, solve_aty); mode = Some Concrete }
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
  (* | DUserTy _  *)
  | DNodes _ | DEdges _ -> (env, d)

(** High-Level Language Type Inference *)
module HLLTypeInf = struct
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
          (* | MGet, [e1; e2] ->
             let e1, mapty = infer_exp e1 |> textract in
             let e2, keyty = infer_exp e2 |> textract in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             texp (eop o [e1; e2], valty, e.espan)
             | MSet, [e1; e2; e3] ->
             let e1, mapty = infer_exp e1 |> textract in
             let e2, keyty = infer_exp e2 |> textract in
             let e3, valty = infer_exp e3 |> textract in
             let ty = TMap (keyty, valty) in
             unify info e mapty ty;
             texp (eop o [e1; e2; e3], ty, e.espan)
             | MCreate, [e1] ->
             let e1, valty = infer_exp e1 |> textract in
             let keyty = fresh_tyvar () in
             texp (eop o [e1], TMap (keyty, valty), e.espan)
             | MMap, [e1; e2] ->
             let e1, fty = infer_exp e1 |> textract in
             let e2, mapty = infer_exp e2 |> textract in
             let keyty = fresh_tyvar () in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e fty (TArrow (valty, valty));
             texp (eop o [e1; e2], mapty, e.espan)
             | MMapFilter, [e1; e2; e3] ->
             let e1, kty = infer_exp e1 |> textract in
             let e2, vty = infer_exp e2 |> textract in
             let e3, mapty = infer_exp e3 |> textract in
             let keyty = fresh_tyvar () in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e kty (TArrow (keyty, TBool));
             unify info e vty (TArrow (valty, valty));
             texp (eop o [e1; e2; e3], mapty, e.espan)
             | MMapIte, [e1; e2; e3; e4] ->
             let e1, kty = infer_exp e1 |> textract in
             let e2, vty1 = infer_exp e2 |> textract in
             let e3, vty2 = infer_exp e3 |> textract in
             let e4, mapty = infer_exp e4 |> textract in
             let keyty = fresh_tyvar () in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e kty (TArrow (keyty, TBool));
             unify info e vty1 (TArrow (valty, valty));
             unify info e vty2 (TArrow (valty, valty));
             texp (eop o [e1; e2; e3; e4], mapty, e.espan)
             | MForAll, [e1; e2; e3] ->
             let e1, kty = infer_exp e1 |> textract in
             let e2, vty = infer_exp e2 |> textract in
             let e3, mapty = infer_exp e3 |> textract in
             let keyty = fresh_tyvar () in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e kty (TArrow (keyty, TBool));
             unify info e vty (TArrow (valty, TBool));
             texp (eop o [e1; e2; e3], TBool, e.espan)
             | MMerge, _ ->
             let (e1, e2, e3), rest =
              match es with
              | [e1; e2; e3] -> (e1, e2, e3), None
              | [e1; e2; e3; el0; el1; er0; er1] -> (e1, e2, e3), Some (el0, el1, er0, er1)
              | _ ->
                Console.error_position
                  info
                  e.espan
                  (Printf.sprintf "invalid number of parameters")
             in
             let e1, fty = infer_exp e1 |> textract in
             let e2, mapty1 = infer_exp e2 |> textract in
             let e3, mapty2 = infer_exp e3 |> textract in
             let keyty = fresh_tyvar () in
             let valty = fresh_tyvar () in
             unify info e mapty1 (TMap (keyty, valty));
             unify info e mapty2 (TMap (keyty, valty));
             unify info e fty (TArrow (valty, TArrow (valty, valty)));
             let es =
              match rest with
              | None -> []
              | Some (el0, el1, er0, er1) ->
                let el0, tyl0 = infer_exp el0 |> textract in
                let el1, tyl1 = infer_exp el1 |> textract in
                let er0, tyr0 = infer_exp er0 |> textract in
                let er1, tyr1 = infer_exp er1 |> textract in
                unify info e tyl0 (TOption valty);
                unify info e tyl1 (TOption valty);
                unify info e tyr0 (TOption valty);
                unify info e tyr1 (TOption valty);
                [el0; el1; er0; er1]
             in
             texp (eop o (e1 :: e2 :: e3 :: es), mapty1, e.espan)
             | MFoldNode, [e1; e2; e3] ->
             let e1, fty = infer_exp e1 |> textract in
             let e2, mapty = infer_exp e2 |> textract in
             let e3, accty = infer_exp e3 |> textract in
             let keyty = TNode in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e fty (TArrow (keyty, TArrow (valty, TArrow (accty, accty))));
             texp (eop o [e1; e2; e3], accty, e.espan)
             | MFoldEdge, [e1; e2; e3] ->
             let e1, fty = infer_exp e1 |> textract in
             let e2, mapty = infer_exp e2 |> textract in
             let e3, accty = infer_exp e3 |> textract in
             let keyty = TEdge in
             let valty = fresh_tyvar () in
             unify info e mapty (TMap (keyty, valty));
             unify info e fty (TArrow (keyty, TArrow (valty, TArrow (accty, accty))));
             texp (eop o [e1; e2; e3], accty, e.espan) *)
          (* | TGet (size, lo, hi), [e1] ->
             let e1, tty = infer_exp e1 |> textract in
             let elt_tyvars = List.map (fun _ -> fresh_tyvar ()) (List.make size ()) in
             unify info e tty (TTuple elt_tyvars);
             let ret_ty =
              if lo = hi
              then List.nth elt_tyvars lo
              else TTuple (List.drop lo elt_tyvars |> List.take (hi - lo + 1))
             in
             texp (eop o [e1], ret_ty, e.espan)
             | TSet (size, lo, hi), [e1; e2] ->
             let e1, tty = infer_exp e1 |> textract in
             let e2, vty = infer_exp e2 |> textract in
             let elt_tyvars = List.map (fun _ -> fresh_tyvar ()) (List.make size ()) in
             unify info e tty (TTuple elt_tyvars);
             if lo = hi
             then unify info e vty (List.nth elt_tyvars lo)
             else
              unify info e vty (TTuple (List.drop lo elt_tyvars |> List.take (hi - lo + 1)));
             texp (eop o [e1; e2], tty, e.espan)
             | MGet, _
             | MSet, _
             | MCreate, _
             | MMap, _
             | MFoldNode, _
             | MFoldEdge, _
             | TGet _, _
             | TSet _, _ ->
             Console.error_position
              info
              e.espan
              (Printf.sprintf "invalid number of parameters") *)
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
          let e, ty_e =
            _infer_exp (i + 1) info (Env.update env x ty_x) record_types body
            |> textract
          in
          unify_opt info e argty ty_x;
          unify_opt info e resty ty_e;
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
          let fun_arg, fun_res =
            match ty_fun.typ with
            | TArrow (fun_arg, fun_res) -> (fun_arg, fun_res)
            | _ ->
                Console.error_position info e.espan
                  "Function must have arrow type"
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

          let ty_res = fresh_tyvar () in
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
                  (* modes should not matter for unification *)
                  unify info e ty_fun
                    (mty None (TArrow (ty_arg, mty None ty_res)));
                  (* set result mode to m2 U m3 *)
                  texp (eapp e1 e2, mty (Some res_mode) ty_res, e.espan) )
          | Multivalue ->
              (* If rule App-M applies *)
              (* modes should not matter for unification *)
              unify info e ty_fun (mty None (TArrow (ty_arg, mty None ty_res)));
              (* Resulting mode is always Multivalue *)
              texp (eapp e1 e2, mty (Some Multivalue) ty_res, e.espan)
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
              | m -> texp (eif e1 e2 e3, mty m ty2.typ, e.espan) )
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
                  texp (eif e1 e2 e3, mty (Some Multivalue) ty2.typ, e.espan)
              | Some m ->
                  (*otherwise it is Symbolic or Multivalue, i.e. Ite-S or Ite-M*)
                  texp (eif e1 e2 e3, mty (Some m) ty2.typ, e.espan)
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
      (* NOTE:  Changes order of evaluation if e is not a value;
         If we have effects, value restriction needed. *)
      (* | ETuple es ->
         let es, tys = infer_exps (i + 1) info env record_types es in
         texp (etuple es, TTuple tys, e.espan)
         | ERecord emap ->
         (* Retrieve the record type corresponding to this expression.
           All record types should be explicitly declared, and
           all labels should appear in exactly one declaration *)
         let open RecordUtils in
         let label = List.hd @@ get_record_labels emap in
         let ferr = Console.error_position info e.espan in
         let tmap = get_type_with_label record_types ferr label in
         if not (same_labels emap tmap)
         then
          (* The only possible record type was not a match *)
          Console.error_position
            info
            e.espan
            "Record does not match any declared record type!";
         let emap = StringMap.map infer_exp emap in
         BatEnum.iter
          (fun l ->
            let e, t1 = StringMap.find l emap |> textract in
            let t2 = StringMap.find l tmap in
            unify info e t1 t2)
          (StringMap.keys emap);
         texp (erecord emap, TRecord tmap, e.espan)
         | EProject (e1, label) ->
         (* Retrieve the record type containing this label.
           All record types should be explicitly declared, and
           all labels should appear in exactly one declaration *)
         let open RecordUtils in
         let ferr = Console.error_position info e.espan in
         let tmap = get_type_with_label record_types ferr label in
         let label_type = StringMap.find label tmap in
         let e1, ety = infer_exp e1 |> textract in
         unify info e1 ety (TRecord tmap);
         texp (eproject e1 label, label_type, e.espan)
         | ESome e ->
         let e, t = infer_exp e |> textract in
         texp (esome e, TOption t, e.espan)
         | EMatch (e1, branches) ->
         let e1, tmatch = infer_exp e1 |> textract in
         let branches, t = infer_branches (i + 1) info env record_types e1 tmatch branches in
         texp (ematch e1 branches, t, e1.espan)
         | ETy (e, t) ->
         let e, t1 = infer_exp e |> textract in
         unify info e t t1;
         texp (ety e t1, t1, e.espan) *)
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

  (* and infer_branches i info env record_types exp tmatch bs =
     match popBranch bs with
     | (p, e), bs when isEmptyBranch bs ->
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
      addBranch p e emptyBranch, t
     | (p, e), bs ->
      let bs, tbranch = infer_branches (i + 1) info env record_types exp tmatch bs in
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
      unify info e t tbranch;
      addBranch p e bs, t

     and infer_pattern i info env e tmatch p =
     valid_pat p;
     match p with
     | PWild -> env
     | PVar x -> Env.update env x tmatch
     | PUnit ->
      unify info e tmatch TUnit;
      env
     | PBool _ ->
      unify info e tmatch TBool;
      env
     | PInt i ->
      unify info e tmatch (tint_of_value i);
      env
     | PNode _ ->
      unify info e tmatch TNode;
      env
     | PEdge (p1, p2) ->
      unify info e tmatch TEdge;
      infer_patterns (i + 1) info env e [TNode; TNode] [p1; p2]
     | PTuple ps ->
      let ts = BatList.map (fun _ -> fresh_tyvar ()) ps in
      let ty = TTuple ts in
      unify info e tmatch ty;
      infer_patterns (i + 1) info env e ts ps
     | PRecord pmap ->
      let ptmap = StringMap.map (fun p -> p, fresh_tyvar ()) pmap in
      let tmap = StringMap.map snd ptmap in
      let ty = TRecord tmap in
      unify info e tmatch ty;
      StringMap.fold (fun _ (p, t) env -> infer_pattern (i + 1) info env e t p) ptmap env
     | POption x ->
      let t = fresh_tyvar () in
      unify info e tmatch (TOption t);
      (match x with
      | None -> env
      | Some p -> infer_pattern (i + 1) info env e t p)

     and infer_patterns i info env e ts ps =
     match ts, ps with
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
     | PWild | PUnit | PBool _ | PInt _ | PNode _ -> env
     | PVar x ->
      (match Env.lookup_opt env x with
      | None -> Env.update env x ()
      | Some _ -> Console.error ("variable " ^ Var.to_string x ^ " appears twice in pattern"))
     | PEdge (p1, p2) -> valid_patterns env [p1; p2]
     | PTuple ps -> valid_patterns env ps
     | PRecord map -> StringMap.fold (fun _ p env -> valid_pattern env p) map env
     | POption None -> env
     | POption (Some p) -> valid_pattern env p

     and valid_patterns env p =
     match p with
     | [] -> env
     | p :: ps -> valid_patterns (valid_pattern env p) ps
     ;; *)
  let infer_declarations info (ds : declarations) : declarations =
    (* let record_types = get_record_types ds in *)
    let record_types = () in
    infer_declarations_aux true infer_exp 0 info Env.empty record_types ds
end

(** High-Level Language Type Inference *)
module LLLTypeInf = struct
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
              (*ensure the modes match*)
              let m1 = OCamlUtils.oget @@ get_mode ty1 in
              if m1 = OCamlUtils.oget (get_mode ty2) then
                texp (eop o [ e1; e2 ], mty (Some m1) TBool, e.espan)
              else Console.error_position info e.espan "Mode mismatch"
          | _ ->
              let argtys, resty = op_typ o in
              let es, tys = infer_exps (i + 1) info env record_types es in
              unifies info e argtys tys;
              (* See binop rule from paper *)
              let m1 = get_mode (List.hd tys) in
              if
                List.for_all
                  (fun ty -> OCamlUtils.oget ty.mode = OCamlUtils.oget m1)
                  (List.tl tys)
              then texp (eop o es, mty m1 resty.typ, e.espan)
              else Console.error_position info e.espan "Mode mismatch" )
      | EFun { arg = x; argty; resty; body } ->
          let arg_mode =
            match argty with None -> Some Concrete | Some typ -> get_mode typ
          in
          let ty_x = mty arg_mode (fresh_tyvar ()) in
          let e, ty_e =
            _infer_exp (i + 1) info (Env.update env x ty_x) record_types body
            |> textract
          in
          unify_opt info e argty ty_x;
          unify_opt info e resty ty_e;
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
      | EApp (e1, e2) ->
          (* Based on rules App-C and App-M*)
          (* Type check e1 and e2 *)
          let e1, ty_fun = infer_exp e1 |> textract in
          let e2, ty_arg = infer_exp e2 |> textract in
          let fun_arg, fun_res =
            match ty_fun.typ with
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
          let e1, tcond = infer_exp e1 |> textract in
          let e2, ty2 = infer_exp e2 |> textract in
          let e3, ty3 = infer_exp e3 |> textract in
          (* Unification does not matter for modes *)
          unify info e1 (mty None TBool) tcond;
          unify info e ty2 ty3;

          (* Check the mode *)
          match get_mode tcond with
          | None -> Console.error_position info e.espan "No mode computed"
          | Some Concrete -> (
              (* If rule Ite applies *)
              match (get_mode ty2, get_mode ty3) with
              | (Some m2, Some m3) as m when m2 = m3 ->
                  texp (eif e1 e2 e3, mty (fst m) ty2.typ, e.espan)
              | _ -> Console.error_position info e.espan "Mode mismatch" )
          | Some _ ->
              Console.error_position info e.espan
                "Symbolic/Multivalue guard - mistyped mode in Ite" )
      | ELet (x, e1, e2) ->
          enter_level ();
          let e1, ty_e1 = infer_exp e1 |> textract in
          leave_level ();
          let ty = generalize ty_e1 in
          let e2, ty_e2 =
            _infer_exp (i + 1) info (Env.update env x ty) record_types e2
            |> textract
          in
          texp (elet x e1 e2, ty_e2, e.espan)
      (* NOTE:  Changes order of evaluation if e is not a value;
         If we have effects, value restriction needed. *)
      (* | ETuple es ->
         let es, tys = infer_exps (i + 1) info env record_types es in
         texp (etuple es, TTuple tys, e.espan)
         | ERecord emap ->
         (* Retrieve the record type corresponding to this expression.
           All record types should be explicitly declared, and
           all labels should appear in exactly one declaration *)
         let open RecordUtils in
         let label = List.hd @@ get_record_labels emap in
         let ferr = Console.error_position info e.espan in
         let tmap = get_type_with_label record_types ferr label in
         if not (same_labels emap tmap)
         then
          (* The only possible record type was not a match *)
          Console.error_position
            info
            e.espan
            "Record does not match any declared record type!";
         let emap = StringMap.map infer_exp emap in
         BatEnum.iter
          (fun l ->
            let e, t1 = StringMap.find l emap |> textract in
            let t2 = StringMap.find l tmap in
            unify info e t1 t2)
          (StringMap.keys emap);
         texp (erecord emap, TRecord tmap, e.espan)
         | EProject (e1, label) ->
         (* Retrieve the record type containing this label.
           All record types should be explicitly declared, and
           all labels should appear in exactly one declaration *)
         let open RecordUtils in
         let ferr = Console.error_position info e.espan in
         let tmap = get_type_with_label record_types ferr label in
         let label_type = StringMap.find label tmap in
         let e1, ety = infer_exp e1 |> textract in
         unify info e1 ety (TRecord tmap);
         texp (eproject e1 label, label_type, e.espan)
         | ESome e ->
         let e, t = infer_exp e |> textract in
         texp (esome e, TOption t, e.espan)
         | EMatch (e1, branches) ->
         let e1, tmatch = infer_exp e1 |> textract in
         let branches, t = infer_branches (i + 1) info env record_types e1 tmatch branches in
         texp (ematch e1 branches, t, e1.espan)
         | ETy (e, t) ->
         let e, t1 = infer_exp e |> textract in
         unify info e t t1;
         texp (ety e t1, t1, e.espan) *)
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
          let e1, ty1 = infer_exp e1 |> textract in
          match get_mode ty1 with
          | Some Concrete ->
              texp (etoBdd e1, mty (Some Symbolic) ty1.typ, e.espan)
          | _ ->
              Console.error_position info e.espan
                "ToBdd applied to non concrete expression" )
      | EToMap e1 -> (
          (* Based on rule ToMap of LLL*)
          let e1, ty1 = infer_exp e1 |> textract in
          match get_mode ty1 with
          | Some Concrete ->
              texp (etoMap e1, mty (Some Multivalue) ty1.typ, e.espan)
          | _ ->
              Console.error_position info e.espan
                "ToBdd applied to non concrete expression" )
      | EApplyN (e1, es) ->
          (* Based on rule ApplyN of LLL *)
          let e1, ty1 = infer_exp e1 |> textract in
          let es, tys = infer_exps (i + 1) info env record_types es in

          (* get the types of the function e1*)
          let rec func_tys ty =
            match ty.typ with
            | TArrow (t1, t2) -> t1 :: func_tys t2
            | TVar { contents = Link t } -> func_tys t
            | _ -> [ ty ]
          in
          let ftys = func_tys ty1 in
          let resty = List.last ftys in

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

  (* and infer_branches i info env record_types exp tmatch bs =
     match popBranch bs with
     | (p, e), bs when isEmptyBranch bs ->
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
      addBranch p e emptyBranch, t
     | (p, e), bs ->
      let bs, tbranch = infer_branches (i + 1) info env record_types exp tmatch bs in
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 record_types e |> textract in
      unify info e t tbranch;
      addBranch p e bs, t

     and infer_pattern i info env e tmatch p =
     valid_pat p;
     match p with
     | PWild -> env
     | PVar x -> Env.update env x tmatch
     | PUnit ->
      unify info e tmatch TUnit;
      env
     | PBool _ ->
      unify info e tmatch TBool;
      env
     | PInt i ->
      unify info e tmatch (tint_of_value i);
      env
     | PNode _ ->
      unify info e tmatch TNode;
      env
     | PEdge (p1, p2) ->
      unify info e tmatch TEdge;
      infer_patterns (i + 1) info env e [TNode; TNode] [p1; p2]
     | PTuple ps ->
      let ts = BatList.map (fun _ -> fresh_tyvar ()) ps in
      let ty = TTuple ts in
      unify info e tmatch ty;
      infer_patterns (i + 1) info env e ts ps
     | PRecord pmap ->
      let ptmap = StringMap.map (fun p -> p, fresh_tyvar ()) pmap in
      let tmap = StringMap.map snd ptmap in
      let ty = TRecord tmap in
      unify info e tmatch ty;
      StringMap.fold (fun _ (p, t) env -> infer_pattern (i + 1) info env e t p) ptmap env
     | POption x ->
      let t = fresh_tyvar () in
      unify info e tmatch (TOption t);
      (match x with
      | None -> env
      | Some p -> infer_pattern (i + 1) info env e t p)

     and infer_patterns i info env e ts ps =
     match ts, ps with
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
     | PWild | PUnit | PBool _ | PInt _ | PNode _ -> env
     | PVar x ->
      (match Env.lookup_opt env x with
      | None -> Env.update env x ()
      | Some _ -> Console.error ("variable " ^ Var.to_string x ^ " appears twice in pattern"))
     | PEdge (p1, p2) -> valid_patterns env [p1; p2]
     | PTuple ps -> valid_patterns env ps
     | PRecord map -> StringMap.fold (fun _ p env -> valid_pattern env p) map env
     | POption None -> env
     | POption (Some p) -> valid_pattern env p

     and valid_patterns env p =
     match p with
     | [] -> env
     | p :: ps -> valid_patterns (valid_pattern env p) ps
     ;; *)
  let infer_declarations info (ds : declarations) : declarations =
    (* let record_types = get_record_types ds in *)
    let record_types = () in
    infer_declarations_aux true infer_exp 0 info Env.empty record_types ds
end

let rec equiv_tys ty1 ty2 =
  equal_tys (canonicalize_type ty1) (canonicalize_type ty2)
