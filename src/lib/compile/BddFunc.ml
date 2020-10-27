open Cudd
open ProbNv_lang
open Syntax
open ProbNv_datastructures
open ProbNv_utils
open ProbNv_utils.OCamlUtils
open Collections
open CompileBDDs
open Batteries
module B = BddUtils

(** Computations over BddFunc are done entirely as NV values. *)

(** ** Type of values computed*)
type t =
  | BBool of Bdd.vt (* Boolean BDD *)
  | BInt of Bdd.vt array (* Integer as an array of booleans *)
  | BOption of Bdd.vt * t (* Option of BDD *)
  | Tuple of t list

let rec print (x : t) =
  match x with
  | BBool _ -> "BBool"
  | BInt _ -> "BInt"
  | BOption (_, x) -> Printf.sprintf "BOption[%s]" (print x)
  | Tuple xs -> Collections.printList print xs "[" ";" "]"

let rec equal_t x y =
  match (x, y) with
  | BBool b1, BBool b2 -> Bdd.is_equal b1 b2
  | BInt i1, BInt i2 -> Array.for_all2 Bdd.is_equal i1 i2
  | BOption (t1, x), BOption (t2, y) -> Bdd.is_equal t1 t2 && equal_t x y
  | Tuple ts1, Tuple ts2 -> List.for_all2 equal_t ts1 ts2
  | _, _ -> false

let bdd_of_bool b = if b then Bdd.dtrue B.mgr else Bdd.dfalse B.mgr

(* given a BDD converts it to a MTBDD*)
let wrap_mtbdd bdd =
  match bdd with
  | BBool bdd ->
      let tru = Mtbdd.cst B.mgr B.tbl true in
      let fal = Mtbdd.cst B.mgr B.tbl false in
      Mtbdd.ite bdd tru fal
  | _ -> failwith "Expected a boolean BDD"

(* given a boolean MTBDD converts it to a BDD*)
let bdd_of_mtbdd (map : bool Cudd.Mtbdd.unique Cudd.Vdd.t) =
  Mtbdd.guard_of_leaf B.tbl map true

let mk_int n sz =
  Array.init sz (fun j ->
      let bit = B.get_bit n j in
      bdd_of_bool bit)

let rec default_value ty =
  match ty.typ with
  | TBool -> BBool (Bdd.dfalse B.mgr)
  | TInt size -> BInt (mk_int 0 size)
  | TTuple ts -> Tuple (List.map default_value ts)
  | TOption ty -> BOption (Bdd.dfalse B.mgr, default_value ty)
  | TNode -> BInt (mk_int 0 tnode_sz)
  | TEdge ->
      Tuple [ default_value (concrete TNode); default_value (concrete TNode) ]
  | TVar { contents = Link t } -> default_value t
  | TVar _ | QVar _ | TArrow _ -> failwith "internal error (default_value)"

(** Lifts a value to a BDD*)
let rec toBdd_typ (record_fns : int * int -> 'a -> 'b) (val_ty : ty) (v : 'v) :
    t =
  match val_ty.typ with
  | TBool -> BBool (bdd_of_bool (Obj.magic v))
  | TInt i ->
      let bs = mk_int (Obj.magic v) i in
      BInt bs
  | TNode ->
      let bs = mk_int (Obj.magic v) tnode_sz in
      BInt bs
  | TEdge ->
      let bs1 = mk_int (fst @@ Obj.magic v) tnode_sz in
      let bs2 = mk_int (snd @@ Obj.magic v) tnode_sz in
      Tuple [ BInt bs1; BInt bs2 ]
  | TTuple ts ->
      let n = BatList.length ts in
      let bs =
        BatList.mapi
          (fun i ty ->
            let proj_fun = (i, n) in
            let f_rec = toBdd_typ record_fns ty in
            let proj_val = record_fns proj_fun in
            f_rec (Obj.magic (proj_val v)))
          ts
      in
      Tuple bs
  | TOption ty -> (
      let f = toBdd_typ record_fns ty in
      match Obj.magic v with
      | None -> BOption (Bdd.dfalse B.mgr, default_value ty)
      | Some v' -> BOption (Bdd.dtrue B.mgr, f v') )
  | _ -> failwith "internal error (toBdd)"

let rec toBdd (record_fns : int * int -> 'a -> 'b) ~(vty_id : int) (v : 'a) : t
    =
  let val_ty = TypeIds.get_elt type_store vty_id in
  toBdd_typ record_fns val_ty v

(** if-then-else between BDDs*)
let rec ite (b : t) (x : t) (y : t) : t =
  match (b, x, y) with
  | BBool b, BBool m, BBool n -> BBool (Bdd.ite b m n)
  | BBool b, BInt ms, BInt ns ->
      BInt (Array.map2 (fun m n -> Bdd.ite b m n) ms ns)
  | BBool b1, BOption (tag1, m), BOption (tag2, n) ->
      let tag = Bdd.ite b1 tag1 tag2 in
      BOption (tag, ite b m n)
  | BBool _, Tuple ms, Tuple ns ->
      let ite = List.map2 (fun m n -> ite b m n) ms ns in
      Tuple ite
  | _ -> failwith "internal error (ite)"

(** equality between BDDs*)
let rec eqBdd x y : Bdd.vt =
  match (x, y) with
  | BBool b1, BBool b2 -> Bdd.eq b1 b2
  | BInt bs1, BInt bs2 ->
      Array.fold_lefti
        (fun acc i b1 -> Bdd.dand acc (Bdd.eq b1 bs2.(i)))
        (Bdd.dtrue B.mgr) bs1
  | BOption (tag1, b1), BOption (tag2, b2) ->
      let tags = Bdd.eq tag1 tag2 in
      let values = eqBdd b1 b2 in
      Bdd.dand tags values
  | Tuple xs, Tuple ys ->
      List.fold_left2
        (fun bacc x y -> Bdd.dand (eqBdd x y) bacc)
        (Bdd.dtrue B.mgr) xs ys
  | BBool _, _ | BInt _, _ | BOption _, _ | Tuple _, _ ->
      failwith "internal error (eq)"

let eq x y = BBool (eqBdd x y)

(** Addition between bdds*)
let add xs ys =
  let var3 = ref (Bdd.dfalse B.mgr) in
  let var4 = Array.make (Array.length xs) (Bdd.dfalse B.mgr) in
  let lenxs = Array.length xs in
  for var5 = 0 to lenxs - 1 do
    var4.(var5) <- Bdd.xor xs.(var5) ys.(var5);
    var4.(var5) <- Bdd.xor var4.(var5) !var3;
    let var6 = Bdd.dor xs.(var5) ys.(var5) in
    let var6 = Bdd.dand var6 !var3 in
    let var7 = Bdd.dand xs.(var5) ys.(var5) in
    let var7 = Bdd.dor var7 var6 in
    var3 := var7
  done;
  BInt var4

let add x y =
  match (x, y) with
  | BInt xs, BInt ys -> add xs ys
  | _, _ -> failwith "Expected integers"

(** Bitwise and operation. Requires that the two integers are of the same size. *)
let uand xs ys =
  BInt (Array.init (Array.length xs) (fun i -> Bdd.dand xs.(i) ys.(i)))

let uand xs ys =
  match (xs, ys) with
  | BInt xs, BInt ys -> uand xs ys
  | _, _ -> failwith "Expected integers"

let leq_arr xs ys =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let acc = ref (Bdd.dtrue B.mgr) in
  Array.iter2
    (fun x y -> acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y)))
    xs ys;
  BBool !acc

let leq x y =
  match (x, y) with
  | BInt xs, BInt ys -> leq_arr xs ys
  | _, _ -> failwith "Expected integers"

let lt xs ys =
  match (leq xs ys, eq xs ys) with
  | BBool b1, BBool b2 ->
      let b = Bdd.dand b1 (Bdd.dnot b2) in
      BBool b
  | _ -> failwith "internal error (lt)"

let band x y =
  match (x, y) with
  | BBool x, BBool y -> BBool (Bdd.dand x y)
  | _, _ -> failwith "Expected booleans"

let bor x y =
  match (x, y) with
  | BBool x, BBool y -> BBool (Bdd.dor x y)
  | _, _ -> failwith "Expected booleans"

(** ** Multivalue operations *)

let toMap ~value = Mtbdd.cst B.mgr B.tbl (Obj.magic value)

(* applyN takes as argument an OCaml function over concrete OCaml values and a nu*)
let applyN ~f ~args : 'a Cudd.Mtbdd.unique Cudd.Vdd.t =
  let g _ (arr : 'a Cudd.Mtbdd.unique Cudd.Vdd.t array) :
      'a Cudd.Mtbdd.unique Cudd.Vdd.t option =
    let cst = Array.for_all (fun add -> Mtbdd.is_cst add) arr in
    if cst then
      let res =
        Array.fold_left
          (fun facc add -> Obj.magic (facc (Obj.magic (Mtbdd.dval add))))
          (Obj.magic f) arr
      in
      Some (Mtbdd.cst B.mgr B.tbl (Obj.magic res))
    else None
  in
  let op =
    User.make_opN
      ~memo:Cudd.(Cache (Cache.create (Array.length args)))
      0 (Array.length args) g
  in
  User.apply_opN op [||] args

(** ** Probabilistic part *)

(* Returns a uniform probability based on the given type *)
let uniform_probability_ty ty (g : AdjGraph.t) =
  match ty.typ with
  | TBool -> 1.0 /. 2.0
  | TInt sz -> 1.0 /. float (1 lsl sz)
  | TNode -> 1.0 /. float (AdjGraph.nb_vertex g)
  | TEdge -> 1.0 /. float (AdjGraph.nb_edges g)
  | TTuple _ -> failwith "Only applicable over base types"
  | TOption _ -> failwith "Todo"
  | TArrow _ | QVar _ | TVar _ ->
      failwith "No probabilities over arrow types or type variables"

(* Creates a uniform distribution represented as a MTBDD, 
   given the type of the value.*)
let uniform_distribution (res : t) ty (g : AdjGraph.t) :
    float Cudd.Mtbdd.unique Cudd.Vdd.t =
  let rec aux ty res =
    match (ty.typ, res) with
    | TInt _, _ | TBool, _ ->
        Mtbdd.cst B.mgr B.tbl_probabilities (uniform_probability_ty ty g)
    | TNode, res -> (
        let prob =
          Mtbdd.cst B.mgr B.tbl_probabilities (uniform_probability_ty ty g)
        in
        (* If it's a node type, assign 0 probability to invalid nodes *)
        match lt res (BInt (mk_int (AdjGraph.nb_vertex g) tnode_sz)) with
        | BBool isValidNode ->
            Mtbdd.ite isValidNode prob (Mtbdd.cst B.mgr B.tbl_probabilities 0.0)
        | _ -> failwith "Expected a boolean result from lt computation" )
    | TEdge, Tuple [ u; v ] ->
        let prob =
          Mtbdd.cst B.mgr B.tbl_probabilities (uniform_probability_ty ty g)
        in
        let isValidEdge =
          AdjGraph.fold_edges_e
            (fun e acc ->
              let bs1 = BInt (mk_int (AdjGraph.Edge.src e) tnode_sz) in
              let bs2 = BInt (mk_int (AdjGraph.Edge.dst e) tnode_sz) in
              Bdd.dor acc (Bdd.dand (eqBdd u bs1) (eqBdd v bs2)))
            g (Bdd.dtrue B.mgr)
        in
        (* If it's not a valid edge assign a 0 probability *)
        Mtbdd.ite isValidEdge prob (Mtbdd.cst B.mgr B.tbl_probabilities 0.0)
    | TTuple ts, Tuple rs ->
        let distrs = List.map2 (fun t r -> aux t r) ts rs in
        User.map_opN
          (fun _ (arr : float Cudd.Mtbdd.unique Cudd.Vdd.t array) ->
            let cst = Array.for_all (fun add -> Mtbdd.is_cst add) arr in
            if cst then
              let res =
                Array.fold_left (fun acc add -> acc *. Mtbdd.dval add) 1.0 arr
              in
              Some (Mtbdd.cst B.mgr B.tbl_probabilities res)
            else None)
          [||] (Array.of_list distrs)
    | TOption _, _ -> failwith "todo: probability for options"
    | TTuple _, _ | TEdge, _ | TVar _, _ | QVar _, _ | TArrow _, _ ->
        failwith "Impossible cases"
  in
  aux ty res

(* Given a type creates a BDD representing all possible values of that type*)
let create_value (ty : ty) (g : AdjGraph.t) : t =
  let rec aux ty =
    match ty.typ with
    | TBool -> BBool (B.freshvar ())
    | TInt sz -> BInt (Array.init sz (fun _ -> B.freshvar ()))
    | TNode -> aux (concrete @@ TInt tnode_sz)
    | TEdge -> aux (concrete @@ TTuple [ concrete @@ TNode; concrete @@ TNode ])
    | TTuple ts ->
        let bs =
          List.fold_left
            (fun ls t ->
              let v = aux t in
              v :: ls)
            [] ts
        in
        Tuple (List.rev bs)
    | TOption ty ->
        let tag = B.freshvar () in
        BOption (tag, aux ty)
    (* | TRecord map -> aux i (TTuple (RecordUtils.get_record_entries map))
 *)
    | TArrow _ | QVar _ | TVar _ ->
        failwith
          (Printf.sprintf "internal error (create_value) type:%s\n"
             (Printing.ty_to_string (get_inner_type ty)))
  in
  let typ = get_inner_type ty in
  let symbolic_start = B.getVarsNb () in
  let res = aux ty in
  (* symbolic_end = current_start + (vars_after_aux - vars_before_aux) - 1
                  = symbolic_start + vars_after_aux - symbolic_start - 1 *)
  let symbolic_end = B.getVarsNb () - 1 in
  let distr = uniform_distribution res typ g in
  B.push_symbolic_vars (symbolic_start, symbolic_end, typ, distr);
  res

let create_value (ty_id : int) g : t =
  create_value (TypeIds.get_elt type_store ty_id) g
