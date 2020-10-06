open ProbNv_lang
(** * Translation of HLL to LLL *)

open Syntax
open Printing
open ProbNv_datastructures
open Collections
open ProbNv_utils

module BddBinds = struct
  type t = exp VarMap.t

  let store = ref ExpMap.empty

  let empty () = VarMap.empty

  let fresh (e : exp) : Var.t * exp VarMap.t =
    match ExpMap.Exceptionless.find e !store with
    | Some b -> (b, VarMap.empty)
    | None ->
        let b = Var.fresh "b" in
        store := ExpMap.add e b !store;
        (b, VarMap.add b e VarMap.empty)

  let union rho1 rho2 =
    VarMap.fold (fun k v acc -> VarMap.add k v acc) rho1 rho2

  let isEmpty rho1 = VarMap.is_empty rho1

  let fold = VarMap.fold
end

let fty_mode m =
  match OCamlUtils.oget m with
  | Concrete | Multivalue -> Some Concrete
  | Symbolic -> Some Symbolic

let rec fty (ty : ty) : ty =
  match ty.typ with
  | TVar _ | QVar _ | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = fty_mode (get_mode ty) }
  | TArrow _ -> ty

(* let ty1 = fty ty1 in
   let ty2 = fty ty2 in
   {typ = TArrow (ty1, ty2); mode = fty_mode (get_mode ty)} *)

let opToBddOp op =
  match op with
  | And -> BddAdd
  | Not -> BddNot
  | Eq -> BddEq
  | UAdd _ -> BddAdd
  | ULess _ -> BddLess
  | BddAnd | BddAdd | BddNot | BddEq | BddLess -> op

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

(* Translate according to rules from figure "Compilation judgement for HLL expressions".
Assumes that functions returning [M] have been inlined.
Assumes that local bindings have been inlined in symbolic expressions.
*)
let rec translate (e : exp) : exp * BddBinds.t =
  match e.e with
  | EVar _ ->
      ({ e with ety = Some (fty (OCamlUtils.oget e.ety)) }, BddBinds.empty ())
  | EVal _ -> (e, BddBinds.empty ())
  | EOp (op, es) -> (
      let esl, rs =
        List.fold_right
          (fun e (esl, rs) ->
            let el, r = translate e in
            (liftBdd el :: esl, BddBinds.union r rs))
          es
          ([], BddBinds.empty ())
      in
      match get_mode (OCamlUtils.oget e.ety) with
      | None -> failwith "cannot translate without a mode"
      | Some Symbolic ->
          (* C-BinOp-S *)
          ( {
              e with
              e = (eop (opToBddOp op) esl).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | _ ->
          (* C-BinOp-M *)
          ({ e with ety = Some (fty (OCamlUtils.oget e.ety)) }, rs) )
  | EIf (e1, e2, e3) -> (
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      let el3, r3 = translate e3 in
      let ty1 = OCamlUtils.oget e1.ety in
      let ty2 = OCamlUtils.oget e2.ety in
      let ty3 = OCamlUtils.oget e3.ety in
      let ty = OCamlUtils.oget e.ety in
      match (get_mode ty1, get_mode ty2, get_mode ty3, get_mode ty) with
      | Some Concrete, Some Concrete, Some Concrete, _ ->
          (* C-Ite-C*)
          ( {
              e with
              e = (eif el1 el2 el3).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
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
          let b, r = BddBinds.fresh el1 in
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
              e = (eif el1 el2 el3).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | Some Symbolic, _, _, Some Symbolic ->
          (* C-Ite-S2 *)
          ( {
              e with
              e = (ebddIf el1 el2 el3).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.empty () )
      | _ -> failwith "This case cannot occur per the type system" )
  | EFun { arg = x; body = e1; argty; resty; fmode } ->
      (* C-Lambda *)
      (* We assume we have inlined functions returning multi-values so we can
         assume the set generated will be empty. *)
      let el1, _ = translate e1 in
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
      (el, BddBinds.empty ())
  | EApp (e1, e2) -> (
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      let ty1 = OCamlUtils.oget e1.ety in
      let ty2 = OCamlUtils.oget e2.ety in
      let ty = OCamlUtils.oget e.ety in
      let argty =
        match (OCamlUtils.oget e1.ety).typ with
        | TArrow (argty, _) -> argty
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
      | Some Concrete, Some Concrete, Some Multivalue ->
          (* C-App-M3 *)
          ( {
              e with
              e = (eapp el1 el2).e;
              ety = Some (fty (OCamlUtils.oget e.ety));
            },
            BddBinds.union r1 r2 )
      | _ -> failwith "This case cannot occur per the type system" )
  | ELet (x, e1, e2) ->
      let el1, r1 = translate e1 in
      let el2, r2 = translate e2 in
      ( {
          e with
          e = (elet x el1 el2).e;
          ety = Some (fty (OCamlUtils.oget e.ety));
        },
        BddBinds.union r1 r2 )
  | EBddIf _ | EToBdd _ | EToMap _ | EApplyN _ ->
      failwith "Cannot translate LLL expressions"

(* todo: need to add FV too *)
let buildApply e r =
  let argty = { typ = TBool; mode = Some Concrete } in
  let e', es =
    BddBinds.fold
      (fun x e1 (acc, es) ->
        let resty = acc.ety in
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

let translateDecl d =
  match d with
  | DLet (x, e) ->
      let e', r = translate e in
      if BddBinds.isEmpty r then DLet (x, e') else DLet (x, buildApply e' r)
  | DSolve s -> failwith "todo"
  | DAssert e -> failwith "todo"
  | DNodes _ | DEdges _ | DSymbolic _ -> d

(* List.fold_right (fun (_,rho) acc -> BddBinds.merge rho acc) esl *)

(*
   let e = 0 in if x = e then 0 else 1

   translating this to applyN(fun b -> let e = 0 in if b then 0 else 1, x = e) is
   well-typed in the modified environment, but the translated expression does not
   satisfy the modified environment. We have to inline variables that are used in
   symbolic expressions and are bound by let-ins and matches.
*)
