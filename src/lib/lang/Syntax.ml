(* Abstract syntax of SRP attribute processing expressions *)
open Batteries
open ProbNv_datastructures
open ProbNv_utils.PrimitiveCollections
open ProbNv_utils
open Cudd

type node = int [@@deriving eq, ord]

let tnode_sz = 12

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
  | TTuple of ty list
[@@deriving ord, eq]

and ty = { typ : baseTy; mode : mode option }

and tyvar = Unbound of tyname * level | Link of ty

let rec join_ty ty1 ty2 =
  match (ty1.typ, ty2.typ) with
  | TInt sz1, TInt sz2 when sz1 = sz2 -> { ty1 with mode = join_opts ty1.mode ty2.mode }
  | TBool, TBool | TNode, TNode | TEdge, TEdge -> { ty1 with mode = join_opts ty1.mode ty2.mode }
  | TTuple ts1, TTuple ts2 ->
      {
        typ = TTuple (List.map2 (fun ty1 ty2 -> join_ty ty1 ty2) ts1 ts2);
        mode = join_opts ty1.mode ty2.mode;
      }
  | TArrow _, TArrow _ -> if ty1 = ty2 then ty1 else failwith "cannot join unequal arrow types"
  | TVar { contents = Link ty3 }, _ -> join_ty { ty3 with mode = join_opts ty1.mode ty3.mode } ty2
  | _, TVar { contents = Link ty3 } -> join_ty ty1 { ty3 with mode = join_opts ty2.mode ty3.mode }
  | TVar _, _ | QVar _, _ | TBool, _ | TInt _, _ | TArrow _, _ | TTuple _, _ | TEdge, _ | TNode, _
    ->
      failwith "Cannot join the given types"

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PInt of Integer.t
  | PTuple of pattern list
  (* | POption of pattern option *)
  (* | PRecord of pattern StringMap.t *)
  | PNode of node
  | PEdge of pattern * pattern
[@@deriving ord, eq]

module Pat = struct
  type t = pattern

  let rec isConcretePat p =
    match p with
    | PInt _ | PBool _ | PNode _ -> true
    (* | POption None -> true *)
    | PEdge (p1, p2) -> isConcretePat p1 && isConcretePat p2
    (* | POption (Some p) -> isConcretePat p *)
    | PTuple ps -> BatList.for_all isConcretePat ps
    | _ -> false

  let rec compare p1 p2 =
    match (p1, p2) with
    | PInt n1, PInt n2 -> Pervasives.compare n1 n2
    | PBool b1, PBool b2 -> Pervasives.compare b1 b2
    | PNode n1, PNode n2 -> Pervasives.compare n1 n2
    | PEdge (p1, p2), PEdge (p1', p2') -> Pervasives.compare (p1, p2) (p1', p2')
    (* | POption p1, POption p2 -> Pervasives.compare p1 p2 *)
    | PTuple ps1, PTuple ps2 ->
        BatList.fold_left2
          (fun b p1 p2 ->
            if b = 0 then
              let c = compare p1 p2 in
              if c = 0 then b else c
            else b)
          0 ps1 ps2
    | _, _ -> failwith (Printf.sprintf "No comparison between non-concrete patterns")
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
  | NLess
  | NLeq
  (* Low-Level Language BDD operations *)
  | BddAnd
  | BddOr
  | BddNot
  | BddEq
  | BddAdd of bitwidth
  | BddLess of bitwidth
  | BddLeq of bitwidth
[@@deriving ord, eq, show]

(** HLL values *)
type v =
  | VBool of bool
  | VInt of Integer.t
  | VNode of node
  | VEdge of edge
  | VTuple of value list
  | VClosure of closure
  | VTotalMap of mtbdd
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

and mtbdd = (value Mtbdd.t[@compare fun _ _ -> failwith "Map value comparison not supported"])

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
  (* Low-Level Language expressions *)
  | EBddIf of exp * exp * exp
  | EToBdd of exp
  | EToMap of exp
  | EApplyN of exp * exp list
[@@deriving ord]

and exp = { e : e; ety : ty option; [@compare fun _ _ -> 0] espan : Span.t [@compare fun _ _ -> 0] }
[@@deriving ord]

and func = { arg : var; argty : ty option; resty : ty option; body : exp; fmode : mode option }

and branches = { pmap : exp PatMap.t; plist : (pattern * exp) list }

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

(** * Handling branches *)

let rec is_irrefutable pat =
  match pat with
  | PWild | PVar _ -> true
  | PBool _ | PInt _ | PNode _ | PEdge _ -> false
  | PTuple pats -> List.for_all is_irrefutable pats

(* | POption _ -> false*)
(* | PRecord map -> StringMap.for_all (fun _ p -> is_irrefutable p) map *)

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
  match PatMap.Exceptionless.find p b.pmap with Some e -> Found e | None -> Rest b.plist

let popBranch b =
  if PatMap.is_empty b.pmap then
    match b.plist with [] -> raise Not_found | (p, e) :: bs -> ((p, e), { b with plist = bs })
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
  | TTuple ts1, TTuple ts2 -> List.for_all2 equal_tys ts1 ts2
  | (TBool | TNode | TEdge | TInt _ | TArrow _ | TVar _ | QVar _ | TTuple _), _ -> false

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
  | VTuple vs1, VTuple vs2 -> equal_lists ~cmp_meta vs1 vs2
  | VClosure (e1, f1), VClosure (e2, f2) ->
      let { ty = ty1; value = value1 } = e1 in
      let { ty = ty2; value = value2 } = e2 in
      Env.equal equal_tys ty1 ty2
      && Env.equal (equal_values ~cmp_meta) value1 value2
      && equal_funcs ~cmp_meta f1 f2
  | VTotalMap m1, VTotalMap m2 -> Mtbdd.is_equal m1 m2
  | (VBool _ | VNode _ | VEdge _ | VInt _ | VClosure _ | VTotalMap _ | VTuple _), _ -> false

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
  | ETuple es1, ETuple es2 -> equal_lists_es ~cmp_meta es1 es2
  | EMatch (e1, bs1), EMatch (e2, bs2) ->
      equal_exps ~cmp_meta e1 e2 && equal_branches ~cmp_meta bs1 bs2
  | EVar _, _
  | EVal _, _
  | EOp _, _
  | EFun _, _
  | EApp _, _
  | EIf _, _
  | ELet _, _
  | ETuple _, _
  | EMatch _, _ ->
      false

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

and equal_branches ~cmp_meta bs1 bs2 =
  let rec equal_branches_lst bs1 bs2 =
    match (bs1, bs2) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | (p1, e1) :: bs1, (p2, e2) :: bs2 ->
        equal_patterns p1 p2 && equal_exps ~cmp_meta e1 e2 && equal_branches_lst bs1 bs2
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
  | PTuple ps1, PTuple ps2 -> equal_patterns_list ps1 ps2
  (* | POption None, POption None -> true
     | POption (Some p1), POption (Some p2) -> equal_patterns p1 p2 *)
  (* | PRecord map1, PRecord map2 -> StringMap.equal equal_patterns map1 map2 *)
  | PNode n1, PNode n2 -> n1 = n2
  | PEdge (p1, p2), PEdge (p1', p2') -> equal_patterns p1 p1' && equal_patterns p2 p2'
  | _ -> false

and equal_patterns_list ps1 ps2 =
  match (ps1, ps2) with
  | [], [] -> true
  | _ :: _, [] | [], _ :: _ -> false
  | p1 :: ps1, p2 :: ps2 -> equal_patterns p1 p2 && equal_patterns_list ps1 ps2

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
  | TTuple ts -> List.fold_left (fun acc t -> acc + hash_ty t) 0 ts + 7
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

let hash_map vdd = Mtbdd.size vdd

let rec hash_value ~hash_meta v : int =
  let m = if hash_meta then (19 * hash_opt hash_ty v.vty) + hash_span v.vspan else 0 in
  (19 * hash_v ~hash_meta v.v) + m

and hash_v ~hash_meta v =
  match v with
  | VBool b -> if b then 1 else 0
  | VInt i -> (19 * Integer.to_int i) + 1
  | VNode n -> (19 * n) + 9
  | VEdge (e1, e2) -> (19 * (e1 + (19 * e2))) + 10
  | VTuple vs ->
      let acc = List.fold_left (fun acc v -> acc + hash_value ~hash_meta v) 0 vs in
      (19 * acc) + 3
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
  | VTotalMap m -> (19 * hash_map m) + 2

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
  | ETuple es -> (19 * hash_es ~hash_meta es) + 7
  | EMatch (e, bs) -> (19 * ((19 * hash_exp ~hash_meta e) + hash_branches ~hash_meta bs)) + 9

and hash_var x = hash_string (Var.to_string x)

and hash_es ~hash_meta es = List.fold_left (fun acc e -> acc + hash_exp ~hash_meta e) 0 es

and hash_op op =
  match op with
  | And -> 1
  | Or -> 2
  | Not -> 3
  | Eq -> 4
  | UAdd n -> 11 + n + 256
  | ULess n -> 11 + n + (256 * 3)
  | ULeq n -> 11 + n + (256 * 4)
  | BddAnd -> 8
  | BddOr -> 9
  | BddAdd n -> 11 + n + (256 * 5)
  | BddEq -> 10
  | BddLess n -> 11 + n + (256 * 7)
  | BddNot -> 12
  | NLess -> 14
  | NLeq -> 15

and hash_branches ~hash_meta bs =
  let acc1 =
    BatList.fold_left (fun acc (p, e) -> acc + hash_pattern p + hash_exp ~hash_meta e) 0 bs.plist
  in
  PatMap.fold (fun p e acc -> acc + hash_pattern p + hash_exp ~hash_meta e) bs.pmap acc1

and hash_pattern p =
  match p with
  | PWild -> 1
  | PVar x -> (19 * hash_var x) + 2
  | PBool b -> (19 * if b then 1 else 0) + 3
  | PInt i -> (19 * Integer.to_int i) + 4
  | PTuple ps -> (19 * hash_patterns ps) + 5
  (* | POption None -> 6
     | POption (Some p) -> (19 * hash_pattern p) + 7 *)
  (* | PRecord map ->
         19
         * StringMap.fold
             (fun l p acc -> acc + +hash_string l + hash_pattern p)
             map 0
         + 8
  *)
  | PNode n -> (19 * n) + 9
  | PEdge (p1, p2) -> (19 * (hash_pattern p1 + (19 * hash_pattern p2))) + 10

and hash_patterns ps = List.fold_left (fun acc p -> acc + hash_pattern p) 0 ps

(* Utilities *)

let arity op =
  match op with
  | And | Or -> 2
  | Not -> 1
  | UAdd _ -> 2
  | Eq -> 2
  | ULess _ | ULeq _ | NLeq | NLess -> 2
  | BddAdd _ | BddAnd | BddOr | BddEq | BddLess _ -> 2
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

let vedge e = value (VEdge e)

let vint i = value (VInt i)

let vtuple vs = value (VTuple vs)

let evar x = exp (EVar x)

let e_val v = exp (EVal v)

let eop op es = exp (EOp (op, es))

let efun f = exp (EFun f)

let eapp e1 e2 = exp (EApp (e1, e2))

let eif e1 e2 e3 = exp (EIf (e1, e2, e3))

let elet x e1 e2 = exp (ELet (x, e1, e2))

let etuple es = exp (ETuple es)

let ematch e bs = exp (EMatch (e, bs))

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
  | TVar _ | QVar _ -> failwith "Should be an instantiated type"
  | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode)) }
  | TTuple ts ->
      {
        typ = TTuple (List.map liftSymbolicTy ts);
        mode = Some (liftSymbolicMode (OCamlUtils.oget ty.mode));
      }
  | TArrow (_, _) -> failwith "Cannot lift to symbolic"

let etoBdd e1 =
  let e1' = exp (EToBdd e1) in
  match e1.ety with None -> e1' | Some ty -> aexp (e1', Some (liftSymbolicTy ty), e1.espan)

let liftMultiMode m =
  match m with
  | Concrete -> Multivalue
  | Multivalue -> Multivalue
  | Symbolic -> failwith "Cannot lift symbolic mode"

let rec liftMultiTy ty =
  match ty.typ with
  | TVar { contents = Link typ } -> liftMultiTy typ
  | TVar _ | QVar _ -> failwith "Should be an instantiated type"
  | TBool | TInt _ | TNode | TEdge ->
      { ty with mode = Some (liftMultiMode (OCamlUtils.oget ty.mode)) }
  | TTuple ts ->
      {
        typ = TTuple (List.map liftMultiTy ts);
        mode = Some (liftMultiMode (OCamlUtils.oget ty.mode));
      }
  | TArrow (_, _) -> failwith "Cannot lift to multivalue"

(* TODO: lift multivalue through tuples *)
let etoMap e1 =
  let e1' = exp (EToMap e1) in
  match e1.ety with None -> e1' | Some ty -> aexp (e1', Some (liftMultiTy ty), e1.espan)

let eApplyN e1 es = exp (EApplyN (e1, es))

let deconstructFun exp = match exp.e with EFun f -> f | _ -> failwith "expected a function"

let rec is_value e =
  match e.e with
  | EVal _ -> true
  | ETuple es -> BatList.for_all is_value es
  | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _ | EMatch _
  | EBddIf (_, _, _)
  | EToBdd _ | EToMap _
  | EApplyN (_, _) ->
      false

let rec to_value e = match e.e with EVal v -> v | _ -> failwith "internal error (to_value)"

let exp_of_v x = exp (EVal (value x))

let rec exp_of_value v =
  let e = e_val v in
  { e with ety = v.vty; espan = v.vspan }

(* e must be a literal *)
let rec exp_to_value (e : exp) : value =
  match e.e with
  | EVar _ | EOp _ | EFun _ | EApp _ | EIf _ | ELet _
  | EBddIf (_, _, _)
  | EToBdd _ | EToMap _ | EMatch _
  | EApplyN (_, _) ->
      failwith "Not a literal"
  | EVal v -> v
  | ETuple es -> vtuple (List.map exp_to_value es)

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
