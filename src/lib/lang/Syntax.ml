(* Abstract syntax of SRP attribute processing expressions *)
open Batteries
open ProbNv_datastructures
open ProbNv_utils.PrimitiveCollections
open ProbNv_utils

type node = int [@@deriving eq, ord]

let tnode_sz = 20

type edge = node * node [@@deriving eq, ord]

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
  | Symbolic -> ( match m2 with Concrete | Symbolic -> Some Symbolic | Multivalue -> None )
  | Multivalue -> ( match m2 with Concrete | Multivalue -> Some Multivalue | Symbolic -> None )

let join m1 m2 =
  match join_opt m1 m2 with Some m -> m | None -> failwith "Failed to join the given modes"

let join_opts m1 m2 =
  match (m1, m2) with None, _ -> m2 | _, None -> m1 | Some m1, Some m2 -> join_opt m1 m2

(** Base types in probNV include an execution mode *)
type baseTy =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of bitwidth
  | TNode
  | TEdge
  | TArrow of ty * ty
[@@deriving ord, eq]

and ty = { typ : baseTy; mode : mode option }

and tyvar = Unbound of tyname * level | Link of ty

type op =
  | And
  | Not
  | Eq
  | UAdd of bitwidth
  | ULess of bitwidth
  (* Low-Level Language BDD operations *)
  | BddAnd
  | BddNot
  | BddEq
  | BddAdd
  | BddLess
[@@deriving ord, eq, show]

(** HLL values *)
type v = VBool of bool | VInt of Integer.t | VNode of node | VEdge of edge | VClosure of closure
[@@deriving ord]

and value = {
  v : v;
  vty : ty option; [@compare fun _ _ -> 0]
  vspan : Span.t; [@compare fun _ _ -> 0]
}
[@@deriving ord]
(** Values also encapsulate their type and location information for error reporting*)

and closure = (env * func[@compare fun _ _ -> failwith "Map value comparison not supported"])
[@@deriving ord]

and env = { ty : ty Env.t; value : value Env.t }

(** Expression Language for both HLL + LLL combined *)
and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  (* Low-Level Language expressions *)
  | EBddIf of exp * exp * exp
  | EToBdd of exp
  | EToMap of exp
  | EApplyN of exp * exp list
[@@deriving ord]

and exp = { e : e; ety : ty option; [@compare fun _ _ -> 0] espan : Span.t [@compare fun _ _ -> 0] }
[@@deriving ord]

and func = { arg : var; argty : ty option; resty : ty option; body : exp; fmode : mode option }

(* var_names should be an exp that uses only the EVar and ETuple constructors *)
type solve = { aty : ty option; var_names : exp; init : exp; trans : exp; merge : exp }

type declaration =
  | DLet of var * exp
  | DSymbolic of var * ty
  | DAssert of exp
  | DSolve of solve
  | DNodes of int
  | DEdges of (node * node) list

type declarations = declaration list

(* equality / hashing *)

let equal_spans (s1 : Span.t) (s2 : Span.t) = s1.start = s2.start && s1.finish = s2.finish

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
  | TBool, TBool | TNode, TNode | TEdge, TEdge -> true
  | TInt n1, TInt n2 -> n1 = n2
  | TArrow (t1, t2), TArrow (s1, s2) -> equal_tys t1 s1 && equal_tys t2 s2
  | TVar t1, TVar t2 -> (
      match (!t1, !t2) with
      | Unbound (n1, x1), Unbound (n2, x2) -> Var.equals n1 n2 && x1 = x2
      | Link t1, Link t2 -> equal_tys t1 t2
      | _ -> false )
  | QVar n1, QVar n2 -> Var.equals n1 n2
  | (TBool | TNode | TEdge | TInt _ | TArrow _ | TVar _ | QVar _), _ -> false

and equal_tys ty1 ty2 = ty1.mode = ty2.mode && equal_base_tys ty1.typ ty2.typ

let rec equal_values ~cmp_meta (v1 : value) (v2 : value) =
  let b = equal_vs ~cmp_meta v1.v v2.v in
  if cmp_meta then b && equal_opt equal_tys v1.vty v2.vty && equal_spans v1.vspan v2.vspan else b

and equal_vs ~cmp_meta v1 v2 =
  match (v1, v2) with
  | VBool b1, VBool b2 -> b1 = b2
  | VNode n1, VNode n2 -> n1 = n2
  | VEdge e1, VEdge e2 -> e1 = e2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VClosure (e1, f1), VClosure (e2, f2) ->
      let { ty = ty1; value = value1 } = e1 in
      let { ty = ty2; value = value2 } = e2 in
      Env.equal equal_tys ty1 ty2
      && Env.equal (equal_values ~cmp_meta) value1 value2
      && equal_funcs ~cmp_meta f1 f2
  | (VBool _ | VNode _ | VEdge _ | VInt _ | VClosure _), _ -> false

and equal_lists ~cmp_meta vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | v1 :: vs1, v2 :: vs2 -> equal_values ~cmp_meta v1 v2 && equal_lists ~cmp_meta vs1 vs2

and equal_exps ~cmp_meta (e1 : exp) (e2 : exp) =
  let b = equal_es ~cmp_meta e1.e e2.e in
  if cmp_meta then b && equal_opt equal_tys e1.ety e2.ety && equal_spans e1.espan e2.espan else b

and equal_es ~cmp_meta e1 e2 =
  match (e1, e2) with
  | EVar x1, EVar x2 -> Var.equals x1 x2
  | EVal v1, EVal v2 -> equal_values ~cmp_meta v1 v2
  | EOp (op1, es1), EOp (op2, es2) -> equal_op op1 op2 && equal_lists_es ~cmp_meta es1 es2
  | EFun f1, EFun f2 -> equal_funcs ~cmp_meta f1 f2
  | EApp (e1, e2), EApp (e3, e4) -> equal_exps ~cmp_meta e1 e3 && equal_exps ~cmp_meta e2 e4
  | EIf (e1, e2, e3), EIf (e4, e5, e6) ->
      equal_exps ~cmp_meta e1 e4 && equal_exps ~cmp_meta e2 e5 && equal_exps ~cmp_meta e3 e6
  | ELet (x1, e1, e2), ELet (x2, e3, e4) ->
      Var.equals x1 x2 && equal_exps ~cmp_meta e1 e3 && equal_exps ~cmp_meta e2 e4
  | _, _ -> false

and equal_lists_es ~cmp_meta es1 es2 =
  match (es1, es2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | e1 :: es1, e2 :: es2 -> equal_exps ~cmp_meta e1 e2 && equal_lists_es ~cmp_meta es1 es2

and equal_funcs ~cmp_meta f1 f2 =
  let { arg = x; argty = aty1; resty = rty1; body = e1 } = f1 in
  let { arg = y; argty = aty2; resty = rty2; body = e2 } = f2 in
  let b =
    if cmp_meta then equal_opt equal_tys aty1 aty2 && equal_opt equal_tys rty1 rty2 else true
  in
  b && Var.equals x y && equal_exps ~cmp_meta e1 e2

let hash_string str =
  let acc = ref 7 in
  for i = 0 to String.length str - 1 do
    let c : char = str.[i] in
    acc := (31 * !acc) + int_of_char c
  done;
  !acc

let rec hash_ty ty =
  match ty.typ with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, x) -> hash_string (Var.to_string name) + x
      | Link t -> hash_ty t )
  | QVar name -> 3 + hash_string (Var.to_string name)
  | TBool -> 4
  | TInt _ -> 5
  | TArrow (ty1, ty2) -> 6 + hash_ty ty1 + hash_ty ty2
  | TNode -> 12
  | TEdge -> 13

let hash_span (span : Span.t) = (19 * span.start) + span.finish

let hash_opt h o = match o with None -> 1 | Some x -> (19 * h x) + 2

let hash_string str =
  let acc = ref 7 in
  for i = 0 to String.length str - 1 do
    let c : char = str.[i] in
    acc := (31 * !acc) + int_of_char c
  done;
  !acc

let rec hash_value ~hash_meta v : int =
  let m = if hash_meta then (19 * hash_opt hash_ty v.vty) + hash_span v.vspan else 0 in
  (19 * hash_v ~hash_meta v.v) + m

and hash_v ~hash_meta v =
  match v with
  | VBool b -> if b then 1 else 0
  | VInt i -> (19 * Integer.to_int i) + 1
  | VNode n -> (19 * n) + 9
  | VEdge (e1, e2) -> (19 * (e1 + (19 * e2))) + 10
  | VClosure (e1, _) ->
      let { ty = _; value = v } = e1 in
      let vs = Env.to_list v in
      let acc =
        List.fold_left
          (fun acc (x, v) ->
            let x = hash_string (Var.to_string x) in
            acc + x + hash_value ~hash_meta v)
          0 vs
      in
      (19 * acc) + 5

and hash_exp ~hash_meta e =
  let m = if hash_meta then (19 * hash_opt hash_ty e.ety) + hash_span e.espan else 0 in
  (19 * hash_e ~hash_meta e.e) + m

and hash_e ~hash_meta e =
  match e with
  | EVar x -> hash_var x
  | EVal v -> (19 * hash_value ~hash_meta v) + 1
  | EOp (op, es) -> (19 * ((19 * hash_op op) + hash_es ~hash_meta es)) + 2
  | EFun f ->
      let i = if hash_meta then hash_opt hash_ty f.argty + hash_opt hash_ty f.resty else 0 in
      (19 * ((19 * ((19 * hash_var f.arg) + hash_exp ~hash_meta f.body)) + i)) + 3
  | EApp (e1, e2) -> (19 * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2)) + 4
  | EIf (e1, e2, e3) ->
      19
      * ((19 * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2)) + hash_exp ~hash_meta e3)
      + 5
  | ELet (x, e1, e2) ->
      (19 * ((19 * ((19 * hash_var x) + hash_exp ~hash_meta e1)) + hash_exp ~hash_meta e2)) + 6

and hash_var x = hash_string (Var.to_string x)

and hash_es ~hash_meta es = List.fold_left (fun acc e -> acc + hash_exp ~hash_meta e) 0 es

and hash_op op =
  match op with
  | And -> 1
  (* | Or -> 2 *)
  | Not -> 3
  | Eq -> 4
  | UAdd n -> 11 + n + 256
  | ULess n -> 11 + n + (256 * 3)

(* | UAnd n -> 12 + n + 256 *  5 *)

(* Utilities *)

let arity op = match op with And -> 2 | Not -> 1 | UAdd _ -> 2 | Eq -> 2 | ULess _ -> 2

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

let vedge e = value (VEdge e)

let vint i = value (VInt i)

let evar x = exp (EVar x)

let e_val v = exp (EVal v)

let eop op es = exp (EOp (op, es))

let efun f = exp (EFun f)

let eapp e1 e2 = exp (EApp (e1, e2))

let eif e1 e2 e3 = exp (EIf (e1, e2, e3))

let elet x e1 e2 = exp (ELet (x, e1, e2))

(** BDD expressions constructors*)

let ebddIf e1 e2 e3 = exp (EBddIf (e1, e2, e3))

let etoBdd e1 = exp (EToBdd e1)

let etoMap e1 =
  let e1' = exp (EToMap e1) in
  match e1.ety with
  | None -> e1'
  | Some ty -> aexp (e1', Some { ty with mode = Some Multivalue }, e1.espan)

let eApplyN e1 es = exp (EApplyN (e1, es))

let deconstructFun exp = match exp.e with EFun f -> f | _ -> failwith "expected a function"

let rec is_value e =
  match e.e with EVal _ -> true | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _ -> false

let rec to_value e = match e.e with EVal v -> v | _ -> failwith "internal error (to_value)"

let exp_of_v x = exp (EVal (value x))

let rec exp_of_value v =
  match v.v with
  | VBool _ | VInt _ | VNode _ | VEdge _ | VClosure _ ->
      let e = e_val v in
      { e with ety = v.vty; espan = v.vspan }

(* e must be a literal *)
let rec exp_to_value (e : exp) : value =
  match e.e with
  | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _ -> failwith "Not a literal"
  | EVal v -> v

let func x body = { arg = x; argty = None; resty = None; body; fmode = None }

let funcFull x argty resty fmode body = { arg = x; argty; resty; body; fmode }

let efunc f =
  match (f.argty, f.resty, f.fmode) with
  | Some argty, Some resty, Some m ->
      aexp (exp (EFun f), Some { typ = TArrow (argty, resty); mode = Some m }, Span.default)
  | _, _, _ -> exp (EFun f)

let lam x body = exp (EFun (func x body))

let annot ty e = { e with ety = Some ty; espan = e.espan }

let annotv ty v = { v with vty = Some ty; vspan = v.vspan }

let rec lams params body =
  match params with
  | [] -> failwith "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> failwith "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let get_decl ds f =
  try
    let daty : declaration =
      BatList.find (fun d -> match f d with None -> false | Some _ -> true) ds
    in
    f daty
  with _ -> None

let get_edges ds =
  try Some (BatList.find_map (fun d -> match d with DEdges es -> Some es | _ -> None) ds)
  with Not_found -> None

let get_nodes ds = get_decl ds (fun d -> match d with DNodes i -> Some i | _ -> None)

let get_symbolics ds =
  List.fold_left (fun acc d -> match d with DSymbolic (x, e) -> (x, e) :: acc | _ -> acc) [] ds
  |> List.rev

(* Getting the mode of a type is a bit trickier because of Links. We need to search through
all the links and make sure their modes are compatible and return the most specific one *)
let rec get_mode ty =
  match ty.typ with
  | TVar { contents = Link ty2 } -> join_opts (get_mode ty2) ty.mode
  | _ -> ty.mode

let rec get_inner_type t : ty =
  match t.typ with TVar { contents = Link t } -> get_inner_type t | _ -> t

let bool_of_val (v : value) : bool option = match v.v with VBool b -> Some b | _ -> None

let compare_vs = compare_value

let compare_es = compare_exp
