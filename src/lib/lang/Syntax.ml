(* Abstract syntax of SRP attribute processing expressions *)
open Batteries
open ProbNv_datastructures
open ProbNv_utils.PrimitiveCollections
open ProbNv_utils
open Cudd

type node = int [@@deriving eq, ord]

let tnode_sz = ref 10

let tedge_sz = ref 10

type edge = int [@@deriving eq, ord]

type bitwidth = int [@@deriving eq, ord, show]

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int [@@deriving ord, eq]

type var = Var.t [@@deriving ord, eq]

type tyname = Var.t [@@deriving ord, eq]

(** Execution modes *)
type mode = Symbolic | Concrete | Multivalue [@@deriving ord, eq]

(* Join operations on modes *)
let rec join_opt m1 m2 =
  match m1 with
  | Concrete -> Some m2
  | Symbolic -> (
      match m2 with Concrete | Symbolic -> Some Symbolic | Multivalue -> None )
  | Multivalue -> (
      match m2 with
      | Concrete | Multivalue -> Some Multivalue
      | Symbolic -> None )

let join m1 m2 =
  match join_opt m1 m2 with
  | Some m -> m
  | None -> failwith "Failed to join the given modes"

let join_opts m1 m2 =
  match (m1, m2) with
  | None, _ -> m2
  | _, None -> m1
  | Some m1, Some m2 -> join_opt m1 m2

let joinAll (m : mode list) =
  match m with
  | [] -> failwith "Empty List"
  | m1 :: m -> List.fold_left (fun acc m -> join m acc) m1 m

(** Base types in probNV include an execution mode *)
type baseTy =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of bitwidth
  | TFloat
  | TNode
  | TEdge
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty
  | TRecord of ty StringMap.t
[@@deriving ord, eq]

and ty = { typ : baseTy; mode : mode option }

and tyvar = Unbound of tyname * level | Link of ty

(* Getting the mode of a type is a bit trickier because of Links. We need to search through
all the links and make sure their modes are compatible and return the most specific one *)
let rec get_mode ty =
  match ty.typ with
  | TVar { contents = Link ty2 } -> join_opts (get_mode ty2) ty.mode
  | _ -> ty.mode

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PInt of Integer.t
  | PFloat of float
  | PTuple of pattern list
  | POption of pattern option
  | PRecord of pattern StringMap.t
  | PNode of node
  | PEdge of pattern * pattern
  | PEdgeId of int
[@@deriving ord, eq]

module Pat = struct
  type t = pattern

  let rec isConcretePat p =
    match p with
    | PInt _ | PBool _ | PNode _ | PFloat _ -> true
    | POption None -> true
    | PEdge (p1, p2) -> isConcretePat p1 && isConcretePat p2
    | POption (Some p) -> isConcretePat p
    | PTuple ps -> BatList.for_all isConcretePat ps
    | PRecord ps -> StringMap.for_all (fun _ p -> isConcretePat p) ps
    | _ -> false

  let rec compare p1 p2 =
    match (p1, p2) with
    | PInt n1, PInt n2 -> Pervasives.compare n1 n2
    | PBool b1, PBool b2 -> Pervasives.compare b1 b2
    | PNode n1, PNode n2 -> Pervasives.compare n1 n2
    | PFloat f1, PFloat f2 -> Float.compare f1 f2
    | PEdge (p1, p2), PEdge (p1', p2') -> Pervasives.compare (p1, p2) (p1', p2')
    | POption (Some p1), POption (Some p2) -> compare p1 p2
    | POption None, POption None -> 0
    | POption (Some _), POption None -> 1
    | POption None, POption _ -> -1
    | PTuple ps1, PTuple ps2 ->
        BatList.fold_left2
          (fun b p1 p2 ->
            if b = 0 then
              let c = compare p1 p2 in
              if c = 0 then b else c
            else b)
          0 ps1 ps2
    | PRecord _, PRecord _ -> failwith "todo"
    | _, _ ->
        failwith (Printf.sprintf "No comparison between non-concrete patterns")
end

module PatMap = BatMap.Make (Pat)

type op =
  | And
  | Or
  | Not
  | Eq
  | UAdd of bitwidth
  | ULess of bitwidth
  | ULeq of bitwidth
  | UAnd of bitwidth
  | FAdd
  | FDiv
  | FMul
  | NLess
  | NLeq
  | FLess
  | FLeq
  | ELess
  | ELeq
  | MGet
  | MSet
  | MCreate
  | MSize
  | MMerge
  | TGet of int (* index *) * int (* size *)
  (* Low-Level Language BDD operations *)
  | BddAnd
  | BddOr
  | BddNot
  | BddEq
  | BddAdd of bitwidth
  | BddUAnd of bitwidth
  | BddLess of bitwidth
  | BddLeq of bitwidth
[@@deriving ord, eq, show]

type edgeValues = | Raw of (node * node) | EdgeId of int
[@@deriving ord, eq]
(** HLL values *)
type v =
  | VBool of bool
  | VInt of Integer.t
  | VFloat of float
  | VNode of node
  | VEdge of edgeValues
  | VTuple of value list
  | VClosure of closure
  | VTotalMap of mtbdd
  | VOption of value option
  | VRecord of value StringMap.t
[@@deriving ord]

and value = {
  v : v;
  vty : ty option; [@compare fun _ _ -> 0]
  vspan : Span.t; [@compare fun _ _ -> 0]
}
[@@deriving ord]
(** Values also encapsulate their type and location information for error reporting*)

and closure =
  (env * func
  [@compare fun _ _ -> failwith "Map value comparison not supported"])
[@@deriving ord]

and env = { ty : ty Env.t; value : value Env.t }

and mtbdd =
  (value Mtbddc.t * (ty * (int * int)) option
  [@compare fun _ _ -> failwith "Map value comparison not supported"])

(** Expression Language for both HLL + LLL combined *)
and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EMatch of exp * branches
  | ESome of exp
  | ERecord of exp StringMap.t
  | EProject of exp * string
  (* Low-Level Language expressions *)
  | EBddIf of exp * exp * exp
  | EToBdd of exp
  | EToMap of exp
  | EApplyN of exp * exp list
[@@deriving ord]

and exp = {
  e : e;
  ety : ty option; [@compare fun _ _ -> 0]
  espan : Span.t; [@compare fun _ _ -> 0]
}
[@@deriving ord]

and func = {
  arg : var;
  argty : ty option;
  resty : ty option;
  body : exp;
  fmode : mode option;
}

and branches = { pmap : exp PatMap.t; plist : (pattern * exp) list }

(** ** Syntax for the probabilistic part of the language *)

type probability = float

type distrPattern =
  | DistrPWild
  | DistrPBool of bool
  | DistrPRange of Integer.t * Integer.t
  | DistrPNode of node
  | DistrPEdge of node * node
  | DistrPTuple of distrPattern list

type distrExpr = (distrPattern * probability) list

(* var_names should be an exp that uses only the EVar and ETuple constructors *)
type solve = {
  aty : ty option;
  var_names : exp;
  fib_names : exp;
  init : exp;
  trans : exp;
  merge : exp;
  generate: exp; (* fib generation function *)
}

(* Forwarding declaration *)
type forward = {
  pty : ty option;
  hvty : ty option;
  hety : ty option;
  names_V : exp;
  names_E : exp;
  fwdInit : exp;
  fwdOut : exp;
  fwdIn : exp;
  hinitV : exp;
  hinitE : exp;
  logE : exp;
  logV : exp;
  bot : exp;
}

type declOptions = string list

(* Distributions can be either expressed in a separate language, in ProbNV's language or by default they are considered uniform *)
type distributionExpression = DExpr of distrExpr | Expr of exp | Uniform

type declaration =
  | DLet of (var * exp * declOptions) (* Variable name, expression, inline? *)
  | DSymbolic of (var list) * ty * distributionExpression (*var list for tuples *)
  | DInfer of (string * exp * exp option)
  | DSolve of solve
  | DForward of forward
  | DNodes of int * (node * string) list
  | DEdges of (node * node * int) list
  | DUserTy of var * ty

type declarations = declaration list

let hasOption opt optionList =
  List.exists (fun o -> opt = o) optionList

(** * Handling branches *)

let rec is_irrefutable pat =
  match pat with
  | PWild | PVar _ -> true
  | PBool _ | PInt _ | PNode _ | PEdge _ | POption _ | PEdgeId _ | PFloat _ -> false
  | PTuple pats -> List.for_all is_irrefutable pats
  | PRecord map -> StringMap.for_all (fun _ p -> is_irrefutable p) map

type branchLookup = Found of exp | Rest of (pattern * exp) list

(* adding to the right place won't really work.. *)
let addBranch p e b = { b with plist = (p, e) :: b.plist }

(* f should preserve concrete patterns *)
let mapBranches f b =
  {
    pmap =
      PatMap.fold
        (fun p e pmap ->
          let p, e = f (p, e) in
          PatMap.add p e pmap)
        b.pmap PatMap.empty;
    plist = BatList.map f b.plist;
  }

let iterBranches f b =
  PatMap.iter (fun p e -> f (p, e)) b.pmap;
  BatList.iter f b.plist

let foldBranches f acc b =
  BatList.fold_left
    (fun acc x -> f x acc)
    (PatMap.fold (fun p e acc -> f (p, e) acc) b.pmap acc)
    b.plist

let lookUpPat p b =
  match PatMap.Exceptionless.find p b.pmap with
  | Some e -> Found e
  | None -> Rest b.plist

let popBranch b =
  if PatMap.is_empty b.pmap then
    match b.plist with
    | [] -> raise Not_found
    | (p, e) :: bs -> ((p, e), { b with plist = bs })
  else
    let pe, pmap = PatMap.pop b.pmap in
    (pe, { b with pmap })

let emptyBranch = { pmap = PatMap.empty; plist = [] }

let isEmptyBranch b = PatMap.is_empty b.pmap && BatList.is_empty b.plist

let optimizeBranches b =
  let rec loop map lst =
    match lst with
    | [] -> { pmap = map; plist = [] }
    | (p, e) :: lst' ->
        if Pat.isConcretePat p = true then loop (PatMap.add p e map) lst'
        else { pmap = map; plist = lst }
  in
  loop b.pmap b.plist

let branchToList b = PatMap.fold (fun p e acc -> (p, e) :: acc) b.pmap b.plist

let branchSize b = Printf.printf "%d\n" (PatMap.cardinal b.pmap)

(* equality / hashing *)

let equal_spans (s1 : Span.t) (s2 : Span.t) =
  s1.start = s2.start && s1.finish = s2.finish

let equal_opt e o1 o2 =
  match (o1, o2) with
  | None, None -> true
  | None, Some _ | Some _, None -> false
  | Some x, Some y -> e x y

let rec equal_lists eq_elts lst1 lst2 =
  match (lst1, lst2) with
  | [], [] -> true
  | [], _ :: _ | _ :: _, [] -> false
  | t1 :: ts1, t2 :: ts2 -> eq_elts t1 t2 && equal_lists eq_elts ts1 ts2

let rec equal_base_tys ty1 ty2 =
  match (ty1, ty2) with
  | TBool, TBool | TNode, TNode | TEdge, TEdge | TFloat, TFloat -> true
  | TInt n1, TInt n2 -> n1 = n2
  | TArrow (t1, t2), TArrow (s1, s2) -> equal_tys t1 s1 && equal_tys t2 s2
  | TOption ty1, TOption ty2 -> equal_tys ty1 ty2
  | TVar t1, TVar t2 -> (
      match (!t1, !t2) with
      | Unbound (n1, x1), Unbound (n2, x2) -> Var.equals n1 n2 && x1 = x2
      | Link t1, Link t2 -> equal_tys t1 t2
      | _ -> false )
  | QVar n1, QVar n2 -> Var.equals n1 n2
  | TTuple ts1, TTuple ts2 -> List.for_all2 equal_tys ts1 ts2
  | TRecord map1, TRecord map2 -> StringMap.equal equal_tys map1 map2
  | TMap (t1, t2), TMap (s1, s2) -> equal_tys t1 s1 && equal_tys t2 s2
  | TVar t1, _ -> 
    (match !t1 with
    | Unbound _ -> false
    | Link t1 -> equal_base_tys t1.typ ty2)
  | _, TVar t2 -> 
    (match !t2 with
    | Unbound _ -> false
    | Link t2 -> equal_base_tys ty1 t2.typ)
  | ( ( TBool | TNode | TEdge | TInt _ | TArrow _ | QVar _ | TTuple _
      | TMap _ | TOption _ | TRecord _ | TFloat ),
      _ ) ->
      false

and equal_tys ty1 ty2 = ty1.mode = ty2.mode && equal_base_tys ty1.typ ty2.typ

let rec equal_values ~cmp_meta (v1 : value) (v2 : value) =
  let b = equal_vs ~cmp_meta v1.v v2.v in
  if cmp_meta then
    b && equal_opt equal_tys v1.vty v2.vty && equal_spans v1.vspan v2.vspan
  else b

and equal_vs ~cmp_meta v1 v2 =
  match (v1, v2) with
  | VBool b1, VBool b2 -> b1 = b2
  | VNode n1, VNode n2 -> n1 = n2
  | VEdge e1, VEdge e2 -> e1 = e2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VFloat f1, VFloat f2 -> Float.equal f1 f2
  | VTuple vs1, VTuple vs2 -> equal_lists ~cmp_meta vs1 vs2
  | VClosure (e1, f1), VClosure (e2, f2) ->
      let { ty = ty1; value = value1 } = e1 in
      let { ty = ty2; value = value2 } = e2 in
      Env.equal equal_tys ty1 ty2
      && Env.equal (equal_values ~cmp_meta) value1 value2
      && equal_funcs ~cmp_meta f1 f2
  | VTotalMap (m1, _), VTotalMap (m2, _) -> Mtbddc.is_equal m1 m2
  | VOption vo1, VOption vo2 -> (
      match (vo1, vo2) with
      | None, None -> true
      | None, Some _ -> false
      | Some _, None -> false
      | Some x, Some y -> equal_values ~cmp_meta x y )
  | VRecord map1, VRecord map2 ->
      StringMap.equal (equal_values ~cmp_meta) map1 map2
  | ( ( VBool _ | VNode _ | VEdge _ | VInt _ | VClosure _ | VTotalMap _
      | VTuple _ | VOption _ | VRecord _ | VFloat _ ),
      _ ) ->
      false

and equal_lists ~cmp_meta vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | v1 :: vs1, v2 :: vs2 ->
      equal_values ~cmp_meta v1 v2 && equal_lists ~cmp_meta vs1 vs2

and equal_exps ~cmp_meta (e1 : exp) (e2 : exp) =
  let b = equal_es ~cmp_meta e1.e e2.e in
  if cmp_meta then
    b && equal_opt equal_tys e1.ety e2.ety && equal_spans e1.espan e2.espan
  else b

and equal_es ~cmp_meta e1 e2 =
  match (e1, e2) with
  | EVar x1, EVar x2 -> Var.equals x1 x2
  | EVal v1, EVal v2 -> equal_values ~cmp_meta v1 v2
  | EOp (op1, es1), EOp (op2, es2) ->
      equal_op op1 op2 && equal_lists_es ~cmp_meta es1 es2
  | EFun f1, EFun f2 -> equal_funcs ~cmp_meta f1 f2
  | EApp (e1, e2), EApp (e3, e4) ->
      equal_exps ~cmp_meta e1 e3 && equal_exps ~cmp_meta e2 e4
  | EIf (e1, e2, e3), EIf (e4, e5, e6) ->
      equal_exps ~cmp_meta e1 e4 && equal_exps ~cmp_meta e2 e5
      && equal_exps ~cmp_meta e3 e6
  | ELet (x1, e1, e2), ELet (x2, e3, e4) ->
      Var.equals x1 x2 && equal_exps ~cmp_meta e1 e3
      && equal_exps ~cmp_meta e2 e4
  | ETuple es1, ETuple es2 -> equal_lists_es ~cmp_meta es1 es2
  | ESome e1, ESome e2 -> equal_exps ~cmp_meta e1 e2
  | EMatch (e1, bs1), EMatch (e2, bs2) ->
      equal_exps ~cmp_meta e1 e2 && equal_branches ~cmp_meta bs1 bs2
  | ERecord map1, ERecord map2 ->
      StringMap.equal (equal_exps ~cmp_meta) map1 map2
  | EProject (e1, label1), EProject (e2, label2) ->
      String.equal label1 label2 && equal_exps ~cmp_meta e1 e2
  | EBddIf (e1, e2, e3), EBddIf (e4, e5, e6) ->
      equal_exps ~cmp_meta e1 e4 && equal_exps ~cmp_meta e2 e5
      && equal_exps ~cmp_meta e3 e6
  | EToBdd e1, EToBdd e2 -> equal_exps ~cmp_meta e1 e2
  | EToMap e1, EToMap e2 -> equal_exps ~cmp_meta e1 e2
  | EApplyN (e1, e2), EApplyN (e3, e4) ->
      equal_exps ~cmp_meta e1 e3 && equal_lists_es ~cmp_meta e2 e4
  | EVar _, _
  | EVal _, _
  | EOp _, _
  | EFun _, _
  | EApp _, _
  | EIf _, _
  | ELet _, _
  | ETuple _, _
  | ESome _, _
  | EMatch _, _
  | EBddIf _, _
  | EToMap _, _
  | EToBdd _, _
  | EApplyN _, _
  | ERecord _, _
  | EProject _, _ ->
      false

and equal_lists_es ~cmp_meta es1 es2 =
  match (es1, es2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | e1 :: es1, e2 :: es2 ->
      equal_exps ~cmp_meta e1 e2 && equal_lists_es ~cmp_meta es1 es2

and equal_funcs ~cmp_meta f1 f2 =
  let { arg = x; argty = aty1; resty = rty1; body = e1 } = f1 in
  let { arg = y; argty = aty2; resty = rty2; body = e2 } = f2 in
  let b =
    if cmp_meta then
      equal_opt equal_tys aty1 aty2 && equal_opt equal_tys rty1 rty2
    else true
  in
  b && Var.equals x y && equal_exps ~cmp_meta e1 e2

and equal_branches ~cmp_meta bs1 bs2 =
  let rec equal_branches_lst bs1 bs2 =
    match (bs1, bs2) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | (p1, e1) :: bs1, (p2, e2) :: bs2 ->
        equal_patterns p1 p2 && equal_exps ~cmp_meta e1 e2
        && equal_branches_lst bs1 bs2
  in
  let equal_branches_map bs1 bs2 =
    PatMap.cardinal bs1.pmap = PatMap.cardinal bs2.pmap
    && PatMap.for_all
         (fun p e ->
           match PatMap.Exceptionless.find p bs2.pmap with
           | None -> false
           | Some e' -> equal_exps ~cmp_meta e e')
         bs1.pmap
  in
  equal_branches_map bs1 bs2 && equal_branches_lst bs1.plist bs2.plist

and equal_patterns p1 p2 =
  match (p1, p2) with
  | PWild, PWild -> true
  | PVar x1, PVar x2 -> Var.equals x1 x2
  | PBool b1, PBool b2 -> b1 = b2
  | PInt i, PInt j -> Integer.equal i j
  | PFloat f1, PFloat f2 -> Float.equal f1 f2
  | PTuple ps1, PTuple ps2 -> equal_patterns_list ps1 ps2
  | POption None, POption None -> true
  | POption (Some p1), POption (Some p2) -> equal_patterns p1 p2
  | PRecord map1, PRecord map2 -> StringMap.equal equal_patterns map1 map2
  | PNode n1, PNode n2 -> n1 = n2
  | PEdge (p1, p2), PEdge (p1', p2') ->
      equal_patterns p1 p1' && equal_patterns p2 p2'
  | PEdgeId p1, PEdgeId p2 -> p1 = p2
  | _ -> false

and equal_patterns_list ps1 ps2 =
  match (ps1, ps2) with
  | [], [] -> true
  | _ :: _, [] | [], _ :: _ -> false
  | p1 :: ps1, p2 :: ps2 -> equal_patterns p1 p2 && equal_patterns_list ps1 ps2

(* Utilities *)

let arity op =
  match op with
  | And | Or -> 2
  | Not -> 1
  | UAdd _ | UAnd _ -> 2
  | FAdd | FDiv | FMul -> 2
  | Eq -> 2
  | ULess _ | ULeq _ | NLeq | NLess | ELess | ELeq | FLess | FLeq -> 2
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MSize -> 2
  | MMerge -> 3
  | TGet _ -> 1
  | BddAdd _ | BddUAnd _ | BddAnd | BddOr | BddEq | BddLess _ | BddLeq _ -> 2
  | BddNot -> 1

(* Useful constructors *)

let tint_of_size n = TInt n

let tint_of_value n = TInt (Integer.size n)

let exp e = { e; ety = None; espan = Span.default }

let value v = { v; vty = None; vspan = Span.default }

let aexp (e, t, span) = { e with ety = t; espan = span }

let avalue (v, t, span) = { v with vty = t; vspan = span }

let wrap exp e = { e with ety = exp.ety; espan = exp.espan }

let concrete typ = { typ; mode = Some Concrete }

let symbolic typ = { typ; mode = Some Symbolic }

let multivalue typ = { typ; mode = Some Multivalue }

let mty m typ = { typ; mode = m }

(* Constructors *)

let vbool b = value (VBool b)

let vnode n = value (VNode n)

let vedge e = value (VEdge (EdgeId e))

let vedgeRaw e = value (VEdge (Raw e))

let vint i = value (VInt i)

let vfloat f = value (VFloat f)

let vtuple vs = value (VTuple vs)

let vrecord map = value (VRecord map)

let voption v = value (VOption v)

let evar x = exp (EVar x)

let e_val v = exp (EVal v)

let eop op es = exp (EOp (op, es))

let efun f = exp (EFun f)

let eapp e1 e2 = exp (EApp (e1, e2))

let eif e1 e2 e3 = exp (EIf (e1, e2, e3))

let elet x e1 e2 = exp (ELet (x, e1, e2))

let etuple es = exp (ETuple es)

let eproject e l = exp (EProject (e, l))

let erecord map = exp (ERecord map)

let ematch e bs = exp (EMatch (e, bs))

let esome e = exp (ESome e)

let vmap m ty = avalue (value (VTotalMap m), ty, Span.default)

(** BDD expressions constructors*)

let ebddIf e1 e2 e3 = exp (EBddIf (e1, e2, e3))

let liftSymbolicMode m =
  match m with
  | Concrete -> Symbolic
  | Symbolic -> Symbolic
  | Multivalue -> failwith "Cannot lift multivalue mode"

let rec liftSymbolicTy ty =
  match ty.typ with
  | TVar { contents = Link typ } -> liftSymbolicTy typ
  | TVar _ | QVar _ -> { ty with mode = Some Symbolic }
  | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode)) }
  | TTuple ts ->
      {
        typ = TTuple (List.map liftSymbolicTy ts);
        mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode));
      }
  | TRecord ts ->
      {
        typ = TRecord (StringMap.map liftSymbolicTy ts);
        mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode));
      }
  | TOption ty ->
      {
        typ = TOption (liftSymbolicTy ty);
        mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode));
      }
  | TMap (_, _) | TArrow (_, _) | TFloat -> 
      failwith "Cannot lift to symbolic"

let etoBdd e1 =
  let e1' = exp (EToBdd e1) in
  match e1.ety with
  | None -> e1'
  | Some ty -> aexp (e1', Some (liftSymbolicTy ty), e1.espan)

let liftMultiMode m =
  match m with
  | Concrete -> Multivalue
  | Multivalue -> Multivalue
  | Symbolic -> failwith "Cannot lift symbolic mode"

let rec liftMultiTy ty =
  match ty.typ with
  | TVar { contents = Link typ } -> liftMultiTy typ
  | TVar _ | QVar _ -> failwith "Should be an instantiated type"
  | TBool | TInt _ | TNode | TEdge | TFloat ->
      { ty with mode = Some (liftMultiMode (OCamlUtils.oget ty.mode)) }
  | TTuple ts ->
      {
        typ = TTuple (List.map liftMultiTy ts);
        mode = Some (liftMultiMode (OCamlUtils.oget ty.mode));
      }
  | TOption ty ->
      {
        typ = TOption (liftMultiTy ty);
        mode = Some (liftMultiMode (OCamlUtils.oget ty.mode));
      }
  | TRecord ts ->
      {
        typ = TRecord (StringMap.map liftMultiTy ts);
        mode = Some (liftMultiMode (OCamlUtils.oget ty.mode));
      }
  | TMap (_, _) ->
      { ty with mode = Some (liftMultiMode (OCamlUtils.oget @@ get_mode ty)) }
  | TArrow (_, _) -> failwith "Cannot lift to multivalue"

let liftMode m m' =
  match join_opt m m' with None -> failwith "Cannot lift mode" | Some _ -> m

let rec liftTy m ty =
  match ty.typ with
  | TVar { contents = Link typ } -> liftTy m typ
  | TVar _ | QVar _ -> ty
  | TBool | TInt _ | TNode | TEdge | TFloat ->
      { ty with mode = Some (liftMode m (OCamlUtils.oget ty.mode)) }
  | TTuple ts ->
      {
        typ = TTuple (List.map (liftTy m) ts);
        mode = Some (liftMode m (OCamlUtils.oget ty.mode));
      }
  | TOption ty ->
      {
        typ = TOption (liftTy m ty);
        mode = Some (liftMode m (OCamlUtils.oget ty.mode));
      }
  | TRecord ts ->
      {
        typ = TRecord (StringMap.map (liftTy m) ts);
        mode = Some (liftMode m (OCamlUtils.oget ty.mode));
      }
  | TMap (_, _) ->
      { ty with mode = Some (liftMode m (OCamlUtils.oget @@ get_mode ty)) }
  | TArrow (ty1, ty2) ->
      {
        typ = TArrow (ty1, ty2);
        mode = Some (liftMode m (OCamlUtils.oget ty.mode));
      }

let etoMap e1 =
  let e1' = exp (EToMap e1) in
  match e1.ety with
  | None -> e1'
  | Some ty -> aexp (e1', Some (liftMultiTy ty), e1.espan)

let eApplyN e1 es = exp (EApplyN (e1, es))

let deconstructFun exp =
  match exp.e with EFun f -> f | _ -> failwith "expected a function"

let rec is_value e =
  match e.e with
  | EVal _ -> true
  | ETuple es -> BatList.for_all is_value es
  | ERecord map -> StringMap.for_all (fun _ e -> is_value e) map
  | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _ | EMatch _ | EProject _
  | EBddIf (_, _, _)
  | ESome _ | EToBdd _ | EToMap _
  | EApplyN (_, _) ->
      false

let rec to_value e =
  match e.e with EVal v -> v | _ -> failwith "internal error (to_value)"

let exp_of_v x = exp (EVal (value x))

let rec exp_of_value v =
  let e = e_val v in
  { e with ety = v.vty; espan = v.vspan }

(* e must be a literal *)
let rec exp_to_value (e : exp) : value =
  match e.e with
  | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _ | ESome _
  | EBddIf (_, _, _)
  | EToBdd _ | EToMap _ | EMatch _ | EProject _
  | EApplyN (_, _) ->
      failwith "Not a literal"
  | EVal v -> v
  | ETuple es -> vtuple (List.map exp_to_value es)
  | ERecord map -> vrecord (StringMap.map exp_to_value map)

let func x body = { arg = x; argty = None; resty = None; body; fmode = None }

let funcFull x argty resty fmode body = { arg = x; argty; resty; body; fmode }

let efunc f =
  match (f.argty, f.resty, f.fmode) with
  | Some argty, Some resty, Some m ->
      aexp
        ( exp (EFun f),
          Some { typ = TArrow (argty, resty); mode = Some m },
          Span.default )
  | _, _, _ -> exp (EFun f)

let lam x body = exp (EFun (func x body))

let annot ty e = { e with ety = Some ty; espan = e.espan }

let annotv ty v = { v with vty = Some ty; vspan = v.vspan }

let rec lams params body =
  match params with
  | [] -> failwith "lams: no parameters"
  | [ p ] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> failwith "apps: no arguments"
  | [ a ] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let get_decl ds f =
  try
    let daty : declaration =
      BatList.find (fun d -> match f d with None -> false | Some _ -> true) ds
    in
    f daty
  with _ -> None

let get_edges ds =
  try
    Some
      (BatList.find_map
         (fun d -> match d with DEdges es -> Some es | _ -> None)
         ds)
  with Not_found -> None

let get_nodes ds =
  get_decl ds (fun d ->
      match d with DNodes (i, xs) -> Some (i, xs) | _ -> None)

let get_symbolics ds =
  List.fold_left
    (fun acc d ->
      match d with DSymbolic (x, ty, prob) -> (x, ty, prob) :: acc | _ -> acc)
    [] ds
  |> List.rev

let get_solves ds =
  List.filter_map (fun d -> match d with DSolve a -> Some a | _ -> None) ds

let rec get_inner_type t : ty =
  match t.typ with TVar { contents = Link t } -> get_inner_type t | _ -> t

let bool_of_val (v : value) : bool option =
  match v.v with VBool b -> Some b | _ -> None

let get_record_types ds =
  List.fold_left
    (fun acc d ->
      match d with DUserTy (_, { typ = TRecord lst }) -> lst :: acc | _ -> acc)
    [] ds

let compare_vs = compare_value

let compare_es = compare_exp

let nb_bits i = Z.log2up (Z.of_int i)

let edge_mapping = ref IntMap.empty

let node_mapping : string IntMap.t ref = ref IntMap.empty

(* Create mapping between edge labels and edges, and node ids and router names, and sets the number of bits required
to represent the edges and nodes in the network *)
let create_topology_mapping nodes topology =
  tnode_sz := nb_bits (AdjGraph.nb_vertex topology);
  tedge_sz := nb_bits (AdjGraph.nb_edges topology);
  edge_mapping :=
    AdjGraph.fold_edges_e
      (fun e acc ->
        IntMap.add (AdjGraph.E.label e) (AdjGraph.E.src e, AdjGraph.E.dst e) acc)
      topology IntMap.empty;
  node_mapping :=
    List.fold_left (fun acc (uid, u) -> IntMap.add uid u acc) IntMap.empty nodes


(* Hashing values for MTBDDs *)

let hash_span (span : Span.t) = (19 * span.start) + span.finish
let hash_opt h o = match o with None -> 1 | Some x -> (19 * h x) + 2
let rec hash_ty ty =
  match ty.typ with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, x) -> Hashtbl.hash (Var.to_string name) + x
      | Link t -> hash_ty t )
  | QVar name -> 3 + Hashtbl.hash (Var.to_string name)
  | TBool -> 4
  | TInt _ -> 5
  | TArrow (ty1, ty2) -> 6 + hash_ty ty1 + hash_ty ty2
  | TTuple ts -> List.fold_left (fun acc t -> acc + hash_ty t) 0 ts + 7
  | TOption t -> 8 + hash_ty t
  | TMap (ty1, ty2) -> 9 + hash_ty ty1 + hash_ty ty2
  | TNode -> 12
  | TEdge -> 13
  | TFloat -> 14
  | TRecord map ->
      StringMap.fold (fun l t acc -> acc + Hashtbl.hash l + hash_ty t) map 0 + 10

  let hash_map vdd = Hashtbl.hash vdd

let rec hash_value ~hash_meta v : int =
  let m =
    if hash_meta then (19 * hash_opt hash_ty v.vty) + hash_span v.vspan else 0
  in
  (19 * hash_v ~hash_meta v.v) + m

and hash_v ~hash_meta v =
  match v with
  | VBool b -> if b then 1 else 0
  | VInt i -> (19 * Integer.to_int i) + 1
  | VFloat i -> (19 * (int_of_float i) + 2)
  | VNode n -> (19 * n) + 9
  | VEdge (Raw (e1, e2)) -> (19 * (e1 + (19 * e2))) + 10
  | VEdge (EdgeId n) -> (19 * n) + 10
  | VTuple vs ->
      let acc =
        List.fold_left (fun acc v -> acc + hash_value ~hash_meta v) 0 vs
      in
      (19 * acc) + 3
  | VOption vo -> (
      match vo with None -> 4 | Some x -> (19 * hash_value ~hash_meta x) + 4 )
  | VClosure (e1, _) ->
      let { ty = _; value = v } = e1 in
      let vs = Env.to_list v in
      let acc =
        List.fold_left
          (fun acc (x, v) ->
            let x = Hashtbl.hash (Var.to_string x) in
            acc + x + hash_value ~hash_meta v)
          0 vs
      in
      (19 * acc) + 5
  | VTotalMap (m, _) -> (19 * hash_map m) + 2
  | VRecord map ->
      let acc =
        StringMap.fold
          (fun l v acc -> acc + Hashtbl.hash l + hash_value ~hash_meta v)
          map 0
      in
      (19 * acc) + 7


(** Used to translate symbolic values to sets of concrete values *)

type 'a valueSet = FullSet | Subset of 'a

type svalue =
| SBool of bool valueSet
| SInt of Integer.t list valueSet
| SNode of node list valueSet
| SEdge of (node * node) list valueSet
| STuple of svalue list