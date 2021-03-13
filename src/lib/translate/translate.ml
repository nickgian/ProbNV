open ProbNv_lang
(** * Translation of HLL to LLL *)

open Syntax
open Printing
open ProbNv_datastructures
open Collections
open ProbNv_utils
open BddBinds
open Typing

(* The function ψ on just the mode part of a type*)
let fty_mode m =
  match OCamlUtils.oget m with
  | Concrete | Multivalue -> Some Concrete
  | Symbolic -> Some Symbolic

(* The function ψ on the whole type*)
let rec fty (ty : ty) : ty =
  match ty.typ with
  | TVar { contents = Link ty } -> fty ty
  | TVar _ | QVar _ | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = fty_mode (get_mode ty) }
  | TOption ty -> { typ = TOption (fty ty); mode = fty_mode (get_mode ty) }
  | TTuple ts ->
      {
        typ =
          TTuple (List.map (fun ty1 -> fty { ty1 with mode = get_mode ty }) ts);
        mode = fty_mode (get_mode ty);
      }
  | TArrow (ty1, ty2) ->
      let ty1 = fty ty1 in
      let ty2 = fty ty2 in
      { typ = TArrow (ty1, ty2); mode = fty_mode (get_mode ty) }
  | TMap (kty, vty) ->
      (* For maps we just canonicalize the types to remove links. *)
      let kty = canonicalize_type kty in
      let vty = canonicalize_type vty in
      { typ = TMap (kty, vty); mode = fty_mode (get_mode ty) }
  | TRecord _ -> failwith "Records should be unrolled"

(* Used for the function arguments when building applyN expressions *)
let rec set_concrete_mode ty =
  match ty.typ with
  | TVar { contents = Link ty } -> set_concrete_mode ty
  | TVar _ | QVar _ | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = Some Concrete }
  | TOption ty -> { typ = TOption (set_concrete_mode ty); mode = Some Concrete }
  | TTuple ts ->
      {
        typ = TTuple (List.map (fun ty1 -> set_concrete_mode ty1) ts);
        mode = Some Concrete;
      }
  | TArrow (ty1, ty2) ->
      let ty1 = set_concrete_mode ty1 in
      let ty2 = set_concrete_mode ty2 in
      { typ = TArrow (ty1, ty2); mode = Some Concrete }
  | TMap (kty, vty) -> { typ = TMap (kty, vty); mode = Some Concrete }
  | TRecord _ -> failwith "Records should be unrolled"

(* Converting normal operations to BDD operations *)
let opToBddOp op =
  match op with
  | And -> BddAnd
  | Or -> BddOr
  | Not -> BddNot
  | Eq -> BddEq
  | UAdd n -> BddAdd n
  | ULess n -> BddLess n
  | ULeq n -> BddLeq n
  | NLess -> BddLess !tnode_sz
  | NLeq -> BddLeq !tnode_sz
  | BddAnd | BddAdd _ | BddOr | BddNot | BddEq | BddLess _ | BddLeq _ -> op
  | MCreate | MGet | MSet | TGet _ ->
      failwith "Can't convert operation to symbolic operation"

let liftBdd e1 =
  let typ = OCamlUtils.oget e1.ety in
  match get_mode typ with
  | Some Concrete ->
      {
        e1 with
        e = (etoBdd e1).e;
        ety = Some { typ = typ.typ; mode = Some Symbolic };
      }
  | Some Symbolic -> e1
  | _ -> failwith "Cannot lift to bdd an expression of this mode"

(* Translate according to the rules from figure "Compilation judgement for HLL
expressions". Assumes that functions returning [M] have been inlined. Assumes
that local bindings have been inlined in symbolic expressions.
*)
let rec translate (e : exp) : exp * BddBinds.t =
  match e.e with
  | EVar _ ->
      ({ e with ety = Some (fty (OCamlUtils.oget e.ety)) }, BddBinds.empty ())
  | EVal _ -> (e, BddBinds.empty ())
  | EOp (op, es) -> (
      match (op, es) with
      | MGet, [ eh1; eh2 ] -> (
          let vty =
            match eh1.ety with
            | Some { typ = TMap (_, vty); mode = _ } -> vty
            | _ -> failwith "Expected a map type"
          in
          match get_mode vty with
          | Some Multivalue ->
              (* C-Map-Get-M*)
              let b, r = BddBinds.fresh e in
              let eb =
                aexp (evar b, Some (fty (OCamlUtils.oget e.ety)), e.espan)
              in
              ({ e with e = eb.e; ety = Some (fty (OCamlUtils.oget e.ety)) }, r)
          | Some Concrete ->
              let el1, r1 = translate eh1 in
              let el2, r2 = translate eh2 in
              ( {
                  e with
                  e = (eop MGet [ el1; el2 ]).e;
                  ety = Some (fty (OCamlUtils.oget e.ety));
                },
                BddBinds.union r1 r2 )
          | _ -> failwith "Expected a map type" )
      | MGet, _ -> failwith "invalid number of arguments to MGet"
      | MSet, [ eh1; eh2; eh3 ] ->
          let el1, r1 = translate eh1 in
          let el2, r2 = translate eh2 in
          let el3, r3 = translate eh3 in
          ( {
              e with
              e = (eop MSet [ el1; el2; el3 ]).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r1 (BddBinds.union r2 r3) )
      | MSet, _ -> failwith "invalid number of arguments to MSet"
      | MCreate, [ eh1 ] ->
          let el1, r1 = translate eh1 in
          ( {
              e with
              e = (eop MCreate [ el1 ]).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r1 )
      | MCreate, _ -> failwith "invalid number of arguments to MCreate"
      | TGet (i, sz), [ eh1 ] ->
          let el1, r1 = translate eh1 in
          ( {
              e with
              e = (eop (TGet (i, sz)) [ el1 ]).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r1 )
      | TGet _, _ -> failwith "invalid number of arguments to TGet"
      | And, _
      | Or, _
      | Not, _
      | Eq, _
      | UAdd _, _
      | ULess _, _
      | ULeq _, _
      | NLess, _
      | NLeq, _ -> (
          let esl, rs =
            List.fold_right
              (fun e (esl, rs) ->
                let el, r = translate e in
                (el :: esl, BddBinds.union r rs))
              es
              ([], BddBinds.empty ())
          in
          match get_mode (OCamlUtils.oget e.ety) with
          | None -> failwith "cannot translate without a mode"
          | Some Symbolic ->
              (* C-BinOp-S *)
              ( {
                  e with
                  e = (eop (opToBddOp op) (List.map liftBdd esl)).e;
                  ety = Some (fty (OCamlUtils.oget e.ety));
                },
                BddBinds.empty () )
          | _ ->
              (* C-BinOp-M *)
              ( {
                  e with
                  e = (eop op esl).e;
                  ety = Some (fty (OCamlUtils.oget e.ety));
                },
                rs ) )
      | (BddAnd | BddOr | BddNot | BddEq | BddAdd _ | BddLess _ | BddLeq _), _
        ->
          failwith "Translation does not apply to LLL constructs" )
  | EIf (e1, e2, e3) -> (
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      let el3, r3 = translate e3 in
      let ty1 = OCamlUtils.oget e1.ety in
      let ty2 = OCamlUtils.oget e2.ety in
      let ty3 = OCamlUtils.oget e3.ety in
      let ty = OCamlUtils.oget e.ety in
      (* Printf.printf "fty: %s \n\n" (Printing.ty_to_string (fty ty)); *)
      match (get_mode ty1, get_mode ty2, get_mode ty3, get_mode ty) with
      | Some Concrete, Some Concrete, Some Concrete, _ ->
          (* C-Ite-C*)
          ( { e with e = (eif el1 el2 el3).e; ety = Some (fty ty) },
            BddBinds.empty () )
      | Some Concrete, _, _, Some Multivalue | Some Multivalue, _, _, _ ->
          (* C-Ite-M1*)
          ( {
              e with
              e = (eif el1 el2 el3).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r1 (BddBinds.union r2 r3) )
      | Some Symbolic, _, _, Some Multivalue ->
          (* C-Ite-M2 *)
          let b, r =
            BddBinds.fresh
              { el1 with ety = Some (fty (OCamlUtils.oget el1.ety)) }
          in
          let eb =
            aexp (evar b, Some { typ = TBool; mode = Some Concrete }, e1.espan)
          in
          ( {
              e with
              e = (eif eb el2 el3).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r (BddBinds.union r2 r3) )
      | Some Concrete, _, _, Some Symbolic ->
          (* C-Ite-S1 *)
          ( {
              e with
              e = (eif el1 (liftBdd el2) (liftBdd el3)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Symbolic, _, _, Some Symbolic ->
          (* C-Ite-S2 *)
          ( {
              e with
              e = (ebddIf el1 (liftBdd el2) (liftBdd el3)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | _ -> failwith "This case cannot occur per the type system" )
  | EFun { arg = x; body = e1; argty; resty; _ } ->
      (* C-Lambda *)
      let el1, r = translate e1 in
      let argty' = fty (OCamlUtils.oget argty) in
      let resty' = fty (OCamlUtils.oget resty) in
      let ty' = fty (OCamlUtils.oget e.ety) in
      let f' =
        {
          arg = x;
          body = el1;
          argty = Some argty';
          resty = Some resty';
          fmode = get_mode ty';
        }
      in
      let el = aexp (efun f', Some (fty (OCamlUtils.oget e.ety)), e.espan) in
      (el, r)
  | EApp (e1, e2) -> (
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      let ty1 = OCamlUtils.oget e1.ety in
      let ty2 = OCamlUtils.oget e2.ety in
      let ty = OCamlUtils.oget e.ety in
      let argty, resty =
        match ty1.typ with
        | TArrow (argty, resty) -> (argty, resty)
        | _ -> failwith "Expected an arrow type"
      in
      match (get_mode argty, get_mode ty2, get_mode ty) with
      | Some Concrete, Some Concrete, Some Concrete ->
          (* C-App-C*)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Concrete, Some Concrete, Some Symbolic ->
          (* C-App-S1*)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Symbolic, Some Symbolic, Some Symbolic ->
          (* C-App-S2 *)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Symbolic, Some Concrete, Some Symbolic ->
          (* C-App-S3 *)
          ( {
              e with
              e = (eapp el1 (liftBdd el2)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Concrete, Some Multivalue, Some Multivalue ->
          (* C-App-M1 *)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r2 )
      | Some Symbolic, Some Symbolic, Some Multivalue ->
          (* C-App-M2 *)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r1 )
      | Some Symbolic, Some Concrete, Some Multivalue ->
          (* C-App-M3 *)
          ( {
              e with
              e = (eapp el1 (liftBdd el2)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r1 )
      | Some Concrete, Some Concrete, Some Multivalue
        when resty.mode = Some Concrete ->
          (* C-App-M4 with an extra check because of solutions modeled as functions. TODO: change that when we get maps. *)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r1 r2 )
      | Some Concrete, Some Concrete, Some Multivalue ->
          (* Because of solutions being functions - change this when we introduce maps it's a total hack TODO*)
          let b, r =
            BddBinds.fresh { e with ety = Some (fty (OCamlUtils.oget e.ety)) }
          in
          let eb = aexp (evar b, Some (fty resty), e1.espan) in
          (eb, BddBinds.union r (BddBinds.union r1 r2))
      | _ -> failwith "This case cannot occur per the type system" )
  | ESome e1 -> (
      let el1, r1 = translate e1 in
      match get_mode (OCamlUtils.oget e.ety) with
      | Some Concrete | Some Multivalue ->
          ( {
              e with
              e = (esome el1).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            r1 )
      | Some Symbolic ->
          ( {
              e with
              e = (liftBdd (esome el1)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | None -> failwith "No mode found in option" )
  | ELet (x, e1, e2) ->
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      ( {
          e with
          e = (elet x el1 el2).e;
          ety = Some (fty (OCamlUtils.oget e.ety));
        },
        BddBinds.union r1 r2 )
  | ETuple es -> (
      let esl, rs =
        List.fold_left
          (fun (acc, accr) e ->
            let el, r = translate e in
            (el :: acc, BddBinds.union r accr))
          ([], BddBinds.empty ())
          es
      in
      match get_mode (OCamlUtils.oget e.ety) with
      | Some Concrete | Some Multivalue ->
          ( {
              e with
              e = (etuple (List.rev esl)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            rs )
      | Some Symbolic ->
          ( {
              e with
              e = (liftBdd (etuple esl)).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            rs )
      | None -> failwith "No mode found in tuple" )
  | EMatch (e1, bs) -> (
      let el1, r1 = translate e1 in
      let ty1 = OCamlUtils.oget e1.ety in
      let ty = OCamlUtils.oget e.ety in
      match (get_mode ty1, get_mode ty) with
      | Some Concrete, Some Concrete ->
          (* C-Match-C*)
          let bsl, _ = translate_branches bs Concrete in
          ( {
              e with
              e = (ematch el1 bsl).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Concrete, Some Multivalue
      | Some Multivalue, Some Multivalue
      | Some Multivalue, Some Concrete ->
          (* C-Match-M1*)
          let bsl, rs = translate_branches bs Multivalue in
          ( {
              e with
              e = (ematch el1 bsl).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r1 rs )
      | Some Symbolic, Some Multivalue ->
          failwith "For now not implementing symbolic matches"
      | Some Concrete, Some Symbolic ->
          let bsl, _ = translate_branches bs Symbolic in
          ( {
              e with
              e = (ematch el1 bsl).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Symbolic, Some Symbolic ->
          failwith "For now not implementing symbolic matches"
      | _ -> failwith "wrong modes" )
  | ERecord _ | EProject _ -> failwith "Records should have been unrolled"
  | EBddIf _ | EToBdd _ | EToMap _ | EApplyN _ ->
      failwith "Cannot translate LLL expressions"

and translate_branches bs mode =
  match popBranch bs with
  | (p, e), bs when isEmptyBranch bs -> (
      let el, r = translate e in
      match mode with
      | Symbolic -> (addBranch p (liftBdd el) emptyBranch, r)
      | _ -> (addBranch p el emptyBranch, r) )
  | (p, e), bs -> (
      let bs, rs = translate_branches bs mode in
      let el, r = translate e in
      match mode with
      | Symbolic -> (addBranch p (liftBdd el) bs, BddBinds.union rs r)
      | _ -> (addBranch p el bs, BddBinds.union rs r) )

let rec pattern_vars p =
  match p with
  | PWild | PBool _ | PInt _ | PNode _ | PEdgeId _ -> VarSet.empty
  | PVar v -> VarSet.singleton v
  | PEdge (p1, p2) -> pattern_vars (PTuple [ p1; p2 ])
  | POption None -> VarSet.empty
  | POption (Some p) -> pattern_vars p
  | PTuple ps ->
      List.fold_left
        (fun set p -> VarSet.union set (pattern_vars p))
        VarSet.empty ps
  | PRecord _ -> failwith "Records should have been unrolled"

(* | PRecord map ->
    StringMap.fold
      (fun _ p set -> PSet.union set (pattern_vars p))
      map
      (PSet.create Var.compare) *)

(* Computing the free variables of an expression typed in multi-value mode  *)
let rec free (seen : VarSet.t) (e : exp) : BddBinds.t =
  match e.e with
  | EVar v ->
      if
        VarSet.mem v seen
        || get_mode @@ OCamlUtils.oget e.ety <> Some Multivalue
      then BddBinds.empty ()
      else BddBinds.singleton v e
  | EVal _ -> BddBinds.empty ()
  | EOp (_, es) | ETuple es ->
      let acc =
        List.fold_left
          (fun set e -> BddBinds.union set (free seen e))
          (BddBinds.empty ()) es
      in
      acc
  | ERecord _ | EProject _ -> failwith "Records should have been unrolled"
  | EFun f -> free (VarSet.add f.arg seen) f.body
  | EApp (e1, e2) -> BddBinds.union (free seen e1) (free seen e2)
  | EIf (e1, e2, e3) ->
      BddBinds.union (free seen e1)
        (BddBinds.union (free seen e2) (free seen e3))
  | ELet (x, e1, e2) ->
      let seen = VarSet.add x seen in
      BddBinds.union (free seen e1) (free seen e2)
  | ESome e -> free seen e
  | EMatch (e, bs) ->
      let bs1 =
        PatMap.fold
          (fun p e set ->
            let seen = VarSet.union seen (pattern_vars p) in
            BddBinds.union set (free seen e))
          bs.pmap (BddBinds.empty ())
      in
      let bs =
        BatList.fold_left
          (fun set (p, e) ->
            let seen = VarSet.union seen (pattern_vars p) in
            BddBinds.union set (free seen e))
          bs1 bs.plist
      in
      BddBinds.union (free seen e) bs
  | EBddIf _ | EToBdd _ | EToMap _ | EApplyN _ ->
      failwith
        "This function is intented to be used with HLL expressions. This is a \
         logic error."

(* | EProject (e, _) -> free seen e
 *)

let free e = free VarSet.empty e

(* Give an expression, and a map of bindings, "closes" the expression using an ApplyN operation *)
let buildApply e r =
  let e', es =
    BddBinds.fold
      (fun x e1 (acc, es) ->
        let resty = acc.ety in
        let argty = set_concrete_mode (OCamlUtils.oget e1.ety) in
        let f =
          {
            arg = x;
            argty = Some argty;
            resty;
            body = acc;
            fmode = Some Concrete;
          }
        in
        let e' =
          aexp
            ( efun f,
              Some
                {
                  typ = TArrow (argty, OCamlUtils.oget resty);
                  mode = Some Concrete;
                },
              acc.espan )
        in
        (e', e1 :: es))
      r (e, [])
  in
  aexp
    ( eApplyN e' es,
      Some { (OCamlUtils.oget e.ety) with mode = Some Multivalue },
      e.espan )

let liftInit init_body aty =
  (* Concrete node argument *)
  let node_arg = Var.fresh "u" in
  let node_ty = concrete TNode in
  (* application:  init_body u*)
  let init_apply =
    aexp
      ( eapp init_body (aexp (evar node_arg, Some node_ty, init_body.espan)),
        Some (fty aty),
        init_body.espan )
  in

  let e1' = etoMap init_apply in
  let resTy = liftMultiTy (OCamlUtils.oget init_apply.ety) in

  let f1 =
    {
      body = e1';
      resty = Some resTy;
      arg = node_arg;
      argty = Some node_ty;
      fmode = Some Concrete;
    }
  in
  aexp
    ( efun f1,
      Some (concrete (TArrow (concrete (OCamlUtils.oget f1.argty).typ, resTy))),
      init_body.espan )

(** translates the [init] function, given the mode [m] of the computed routes.
  [m] can be affected by the other functions, such as trans and merge. *)
let translateInit init aty =
  (* Printf.printf "init aty: %s" (Printing.ty_to_string aty); *)
  let init', r = translate init in
  match init'.e with
  | EFun f ->
      let fv = free init in
      let rho = BddBinds.union r fv in
      if BddBinds.isEmpty rho then
        if (* Printf.printf "bdd binds is empty\n"; *)
           aty.mode = Some Concrete
        then init'
        else
          let e1' = etoMap f.body in
          let resTy = liftMultiTy (OCamlUtils.oget f.resty) in
          aexp
            ( efun { f with body = e1'; resty = Some resTy },
              Some
                (concrete
                   (TArrow (concrete (OCamlUtils.oget f.argty).typ, resTy))),
              init.espan )
      else
        let e1' = buildApply f.body rho in
        let resTy = liftMultiTy (OCamlUtils.oget f.resty) in
        aexp
          ( efun { f with body = e1'; resty = Some resTy },
            Some
              (concrete
                 (TArrow (concrete (OCamlUtils.oget f.argty).typ, resTy))),
            init.espan )
  | _ -> (
      let init_ty = OCamlUtils.oget init.ety in
      match (get_mode init_ty, get_mode aty) with
      | Some Concrete, Some Concrete -> init'
      | Some Concrete, Some Multivalue -> liftInit init' aty
      | _ ->
          failwith "init should have been inlined if it's not of concrete mode"
      )

(* Lifting a transfer function to a multivalue expression *)
let liftTrans trans_body aty =
  (* Concrete edge argument *)
  let edge_arg = Var.fresh "e" in
  let edge_ty = concrete TEdge in
  (* Concrete route argument *)
  let route_arg = Var.fresh "x" in
  let route_concrete_ty = concrete aty.typ in
  (* application:  trans_body edge*)
  let trans_apply =
    aexp
      ( eapp trans_body (aexp (evar edge_arg, Some edge_ty, trans_body.espan)),
        Some (concrete (TArrow (route_concrete_ty, route_concrete_ty))),
        trans_body.espan )
  in
  (* application: trans_body edge x*)
  let trans_apply_2 =
    aexp
      ( eapp trans_apply
          (aexp (evar route_arg, Some route_concrete_ty, trans_body.espan)),
        Some route_concrete_ty,
        trans_body.espan )
  in

  (* abstraction in applyN: fun x -> trans_body edge x *)
  let f1 =
    {
      body = trans_apply_2;
      arg = route_arg;
      argty = Some route_concrete_ty;
      resty = Some route_concrete_ty;
      fmode = Some Concrete;
    }
  in
  let applyN_fun =
    aexp
      ( efun f1,
        Some (concrete (TArrow (route_concrete_ty, route_concrete_ty))),
        trans_body.espan )
  in

  (* arguments in applyN: x *)
  (* aty should be multivalue mode *)
  let route_ty = Some aty in
  let applyN_args = [ aexp (evar route_arg, route_ty, trans_body.espan) ] in
  let applyN_exp =
    aexp (eApplyN applyN_fun applyN_args, route_ty, trans_body.espan)
  in

  (* abstraction over multivalue route: fun x -> applyN ...*)
  let fx =
    {
      body = applyN_exp;
      arg = route_arg;
      argty = route_ty;
      resty = route_ty;
      fmode = Some Concrete;
    }
  in
  let trans_x =
    aexp (efun fx, Some (concrete (TArrow (aty, aty))), trans_body.espan)
  in

  (* abstraction over edge: fun e -> fun x -> applyN *)
  let fe =
    {
      body = trans_x;
      arg = edge_arg;
      argty = Some edge_ty;
      resty = trans_x.ety;
      fmode = Some Concrete;
    }
  in
  aexp
    ( efun fe,
      Some (concrete (TArrow (edge_ty, OCamlUtils.oget trans_x.ety))),
      trans_body.espan )

(** translates the [trans] function, given the mode [m] of the computed routes. *)
let translateTrans trans aty =
  match trans.e with
  | EFun f1 -> (
      match f1.body.e with
      (* fun edge -> trans_expr*)
      | EFun f2 ->
          let eh2 = f2.body in
          (* trans_expr *)
          (* translate the internal expression, i.e. without the arguments *)
          let el2, r = translate eh2 in
          let fv = free eh2 in

          (* combine the bindings from the free variables and any bindings produced by the translation *)
          let rho = BddBinds.union r fv in
          if BddBinds.isEmpty rho then
            if get_mode aty = Some Concrete then
              (* We do not need to change the expressions or modes *)
              let f2' = { f2 with body = el2 } in
              let e2' = aexp (efun f2', f1.body.ety, f1.body.espan) in
              (*fun edge -> trans_expr_lll *)
              aexp (efun { f1 with body = e2' }, trans.ety, trans.espan)
            else liftTrans trans aty
          else
            (*TODO: this code is largely similar with the code above, factor it out? *)
            let el2' = buildApply el2 rho in
            let resTy = liftMultiTy (OCamlUtils.oget el2'.ety) in
            (* also need to lift the input route type*)
            let argTy = liftMultiTy (OCamlUtils.oget f2.argty) in
            let f2' =
              { f2 with body = el2'; resty = Some resTy; argty = Some argTy }
            in
            let e2' =
              aexp
                ( efun f2',
                  Some (concrete (TArrow (argTy, resTy))),
                  f1.body.espan )
            in
            aexp
              ( efun { f1 with body = e2'; resty = e2'.ety },
                Some
                  (concrete
                     (TArrow
                        ( concrete (OCamlUtils.oget f1.argty).typ,
                          OCamlUtils.oget e2'.ety ))),
                trans.espan )
      | _ -> failwith "Trans must be a function" )
  | _ -> (
      let trans_ty = OCamlUtils.oget trans.ety in
      match (get_mode trans_ty, get_mode aty) with
      | Some Concrete, Some Concrete -> trans
      | Some Concrete, Some Multivalue -> liftTrans trans aty
      | _ ->
          failwith "trans should have been inlined if it's not of concrete mode"
      )

let liftMerge merge_body aty =
  (* Concrete node argument *)
  let node_arg = Var.fresh "u" in
  let node_ty = concrete TNode in
  (* Concrete route arguments *)
  let route_arg_x = Var.fresh "x" in
  let route_arg_y = Var.fresh "y" in
  let route_concrete_ty = concrete aty.typ in
  (* application:  merge_body u*)
  let merge_apply =
    aexp
      ( eapp merge_body (aexp (evar node_arg, Some node_ty, merge_body.espan)),
        Some
          (concrete
             (TArrow
                ( route_concrete_ty,
                  concrete (TArrow (route_concrete_ty, route_concrete_ty)) ))),
        merge_body.espan )
  in
  (* application: merge_body u x*)
  let merge_apply_2 =
    aexp
      ( eapp merge_apply
          (aexp (evar route_arg_x, Some route_concrete_ty, merge_body.espan)),
        Some (concrete (TArrow (route_concrete_ty, route_concrete_ty))),
        merge_body.espan )
  in

  (* application: merge_body u x y*)
  let merge_apply_3 =
    aexp
      ( eapp merge_apply_2
          (aexp (evar route_arg_y, Some route_concrete_ty, merge_body.espan)),
        Some route_concrete_ty,
        merge_body.espan )
  in

  (* abstraction in applyN: fun y -> merge_body edge x y *)
  let f1 =
    {
      body = merge_apply_3;
      arg = route_arg_y;
      argty = Some route_concrete_ty;
      resty = Some route_concrete_ty;
      fmode = Some Concrete;
    }
  in
  let applyN_fun_1 =
    aexp
      ( efun f1,
        Some (concrete (TArrow (route_concrete_ty, route_concrete_ty))),
        merge_body.espan )
  in

  (* abstraction in applyN: fun x fun y -> merge_body edge x y *)
  let f2 =
    {
      body = applyN_fun_1;
      arg = route_arg_x;
      argty = Some route_concrete_ty;
      resty = applyN_fun_1.ety;
      fmode = Some Concrete;
    }
  in

  let applyN_fun_2 =
    aexp
      ( efun f2,
        Some
          (concrete
             (TArrow (route_concrete_ty, OCamlUtils.oget applyN_fun_1.ety))),
        merge_body.espan )
  in

  (* arguments in applyN: x *)
  let route_ty = aty in
  let applyN_args =
    [
      aexp (evar route_arg_x, Some route_ty, merge_body.espan);
      aexp (evar route_arg_y, Some route_ty, merge_body.espan);
    ]
  in
  let applyN_exp =
    aexp (eApplyN applyN_fun_2 applyN_args, Some route_ty, merge_body.espan)
  in

  (* abstraction over multivalue route: fun y -> applyN ...*)
  let fy =
    {
      body = applyN_exp;
      arg = route_arg_y;
      argty = Some route_ty;
      resty = Some route_ty;
      fmode = Some Concrete;
    }
  in

  let merge_y =
    aexp
      (efun fy, Some (concrete (TArrow (route_ty, route_ty))), merge_body.espan)
  in

  (* abstraction over multivalue route: fun x -> fun y -> applyN ...*)
  let fx =
    {
      body = merge_y;
      arg = route_arg_x;
      argty = Some route_ty;
      resty = merge_y.ety;
      fmode = Some Concrete;
    }
  in

  let merge_x =
    aexp
      ( efun fx,
        Some (concrete (TArrow (route_ty, OCamlUtils.oget merge_y.ety))),
        merge_body.espan )
  in

  (* abstraction over node: fun u -> fun x -> fun y -> applyN *)
  let fu =
    {
      body = merge_x;
      arg = node_arg;
      argty = Some node_ty;
      resty = merge_x.ety;
      fmode = Some Concrete;
    }
  in
  aexp
    ( efun fu,
      Some (concrete (TArrow (node_ty, OCamlUtils.oget merge_x.ety))),
      merge_body.espan )

(** translates the [merge] function, given the mode [m] of the computed routes. *)
let translateMerge merge aty =
  match merge.e with
  | EFun f1 -> (
      match f1.body.e with
      (* fun u -> f2 *)
      | EFun f2 -> (
          match f2.body.e with
          (* fun x -> f3 *)
          | EFun f3 ->
              (* fun y -> merge_expr *)
              let eh3 = f3.body in
              (* translate the internal expression, i.e. without the arguments *)
              let el3, r = translate eh3 in
              (* combine the bindings from the free variables and any bindings produced by the translation *)
              let fv = free eh3 in
              let rho = BddBinds.union r fv in
              if BddBinds.isEmpty rho then
                if aty.mode = Some Concrete then
                  (* We do not need to change the expressions or modes *)
                  let f3' = { f3 with body = el3 } in
                  let e3' = aexp (efun f3', f2.body.ety, f2.body.espan) in
                  let e2' =
                    aexp
                      (efun { f2 with body = e3' }, f1.body.ety, f1.body.espan)
                  in
                  aexp (efun { f1 with body = e2' }, merge.ety, merge.espan)
                else (* Need to lift to a multivalue *)
                  liftMerge merge aty
              else
                (*TODO: this code is largely similar with the code above, factor it out? *)
                let el3' = buildApply el3 rho in
                (* return type will be the one returned from translation lifted to multi-value *)
                let resTy = liftMultiTy (OCamlUtils.oget el3'.ety) in
                (* also need to lift the input routes type*)
                let argTy2 = liftMultiTy (OCamlUtils.oget f3.argty) in
                let argTy1 = liftMultiTy (OCamlUtils.oget f2.argty) in
                let f3' =
                  {
                    f3 with
                    body = el3';
                    resty = Some resTy;
                    argty = Some argTy2;
                  }
                in
                let e3' =
                  aexp
                    ( efun f3',
                      Some (concrete (TArrow (argTy2, resTy))),
                      f2.body.espan )
                in
                let f2' =
                  { f2 with body = e3'; resty = e3'.ety; argty = Some argTy1 }
                in
                let e2' =
                  aexp
                    ( efun f2',
                      Some (concrete (TArrow (argTy1, OCamlUtils.oget e3'.ety))),
                      f1.body.espan )
                in
                aexp
                  ( efun { f1 with body = e2'; resty = e2'.ety },
                    Some
                      (concrete
                         (TArrow
                            ( concrete (OCamlUtils.oget f1.argty).typ,
                              OCamlUtils.oget e2'.ety ))),
                    merge.espan )
          | _ -> failwith "Merge must be a function" )
      | _ -> failwith "Merge must be a function" )
  | _ -> (
      match (get_mode (OCamlUtils.oget merge.ety), get_mode aty) with
      | Some Concrete, Some Concrete -> merge
      | Some Concrete, Some Multivalue -> liftMerge merge aty
      | _ ->
          failwith "merge should have been inlined if it's not of concrete mode"
      )

let translateDecl d =
  match d with
  | DLet (x, e) ->
      BddBinds.clearStore ();
      let e', r = translate e in
      let fv = free e in
      let rho = BddBinds.union r fv in
      if BddBinds.isEmpty r then DLet (x, e') else DLet (x, buildApply e' rho)
  | DSolve { aty; var_names; init; trans; merge } ->
      let route_ty = OCamlUtils.oget aty in
      BddBinds.clearStore ();
      let init' = translateInit init route_ty in
      BddBinds.clearStore ();
      let trans' = translateTrans trans route_ty in
      BddBinds.clearStore ();
      let merge' = translateMerge merge route_ty in
      DSolve { aty; var_names; init = init'; trans = trans'; merge = merge' }
  | DAssert (e, prob) ->
      BddBinds.clearStore ();
      let e', r = translate e in
      let fv = free e in
      let rho = BddBinds.union r fv in
      if BddBinds.isEmpty rho then DAssert (e', prob)
      else DAssert (buildApply e' rho, prob)
  | DNodes _ | DEdges _ | DSymbolic _ | DUserTy _ -> d

let translate_declarations ds = List.map translateDecl ds

(* List.fold_right (fun (_,rho) acc -> BddBinds.merge rho acc) esl *)

(*
   let e = 0 in if x = e then 0 else 1

   translating this to applyN(fun b -> let e = 0 in if b then 0 else 1, x = e) is
   well-typed in the modified environment, but the translated expression does not
   satisfy the modified environment. We have to inline variables that are used in
   symbolic expressions and are bound by let-ins and matches.
*)
