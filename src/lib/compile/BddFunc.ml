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
type 'a t =
  | BBool of Bdd.vt (* Boolean BDD *)
  | BInt of Bdd.vt array (* Integer as an array of booleans *)
  | BOption of Bdd.vt * 'a t (* Option of BDD *)
  | Tuple of 'a t list

let rec print (x : 'a t) =
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
let bdd_of_mtbdd (map : bool Cudd.Mtbdd.unique Cudd.Vdd.t) = Mtbdd.guard_of_leaf B.tbl map true

(* Todo: will probably require record_fns when we add tuples *)

(** Lifts a value to a BDD*)
let rec toBdd (_ : int * int -> 'a -> 'b) ~(vty_id : int) (v : 'v) : 'v t =
  let val_ty = TypeIds.get_elt type_store vty_id in
  match val_ty.typ with
  | TBool -> BBool (bdd_of_bool (Obj.magic v))
  | TInt i ->
      let bs =
        Array.init i (fun j ->
            let bit = B.get_bit (Obj.magic v) j in
            bdd_of_bool bit)
      in
      BInt bs
  | TNode ->
      let bs =
        Array.init tnode_sz (fun j ->
            let bit = B.get_bit (Obj.magic v) j in
            bdd_of_bool bit)
      in
      BInt bs
  | TEdge ->
      let bs1 =
        Array.init tnode_sz (fun j ->
            let bit = B.get_bit (fst (Obj.magic v)) j in
            bdd_of_bool bit)
      in
      let bs2 =
        Array.init tnode_sz (fun j ->
            let bit = B.get_bit (snd (Obj.magic v)) j in
            bdd_of_bool bit)
      in
      Tuple [BInt bs1; BInt bs2]
  (* | VOption None ->
         let ty =
           match get_inner_type (oget v.vty) with
           | TOption ty -> ty
           | _ -> failwith "internal error (eval_value)"
         in
         let dv = BddMap.default_value ty in
         BOption (Bdd.dfalse B.mgr, eval_value dv)
     | VOption (Some v) -> BOption (Bdd.dtrue B.mgr, eval_value v)
     | VTuple vs -> Tuple (List.map eval_value vs) *)
  | _ -> failwith "internal error (toBdd)"

(** if-then-else between BDDs*)
let rec ite (b : 'a t) (x : 'a t) (y : 'a t) : 'a t =
  match (b, x, y) with
  | BBool b, BBool m, BBool n -> BBool (Bdd.ite b m n)
  | BBool b, BInt ms, BInt ns -> BInt (Array.map2 (fun m n -> Bdd.ite b m n) ms ns)
  (* | BBool b, BOption (tag1, m), BOption (tag2, n) ->
      let tag = Bdd.ite b tag1 tag2 in
      BOption (tag, ite b m n) *)
  | BBool _, Tuple ms, Tuple ns ->
      let ite = List.map2 (fun m n -> ite b m n) ms ns in
      Tuple ite
  | _ -> failwith "internal error (ite)"

(** equality between BDDs*)
let rec eq x y : Bdd.vt =
  match (x, y) with
  | BBool b1, BBool b2 -> Bdd.eq b1 b2
  | BInt bs1, BInt bs2 ->
      Array.fold_lefti (fun acc i b1 -> Bdd.dand acc (Bdd.eq b1 bs2.(i))) (Bdd.dtrue B.mgr) bs1
  | BOption (tag1, b1), BOption (tag2, b2) ->
      let tags = Bdd.eq tag1 tag2 in
      let values = eq b1 b2 in
      Bdd.dand tags values
  | Tuple xs, Tuple ys ->
      List.fold_left2 (fun bacc x y -> Bdd.dand (eq x y) bacc) (Bdd.dtrue B.mgr) xs ys
  | _ -> failwith "internal error (eq)"

let eq x y = BBool (eq x y)

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
  match (x, y) with BInt xs, BInt ys -> add xs ys | _, _ -> failwith "Expected integers"

(** Bitwise and operation. Requires that the two integers are of the same size. *)
let uand xs ys = BInt (Array.init (Array.length xs) (fun i -> Bdd.dand xs.(i) ys.(i)))

let uand xs ys =
  match (xs, ys) with BInt xs, BInt ys -> uand xs ys | _, _ -> failwith "Expected integers"

let leq_arr xs ys =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let acc = ref (Bdd.dtrue B.mgr) in
  Array.iter2 (fun x y -> acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))) xs ys;
  BBool !acc

let leq x y =
  match (x, y) with BInt xs, BInt ys -> leq_arr xs ys | _, _ -> failwith "Expected integers"

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

(** ** Multivalue operations *)

let toMap ~value = Mtbdd.cst B.mgr B.tbl (Obj.magic value)

(* applyN takes as argument an OCaml function over concrete OCaml values and a nu*)
let applyN ~f ~args : 'a Cudd.Mtbdd.unique Cudd.Vdd.t =
  let g _ (arr : 'a Cudd.Mtbdd.unique Cudd.Vdd.t array) : 'a Cudd.Mtbdd.unique Cudd.Vdd.t option =
    let cst = Array.fold_left (fun res add -> res && Mtbdd.is_cst add) true arr in
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
    User.make_opN ~memo:Cudd.(Cache (Cache.create (Array.length args))) 0 (Array.length args) g
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
  | TArrow _ | QVar _ | TVar _ -> failwith "No probabilities over arrow types or type variables"

(* Creates a uniform distribution represented as a MTBDD, given the type of the value.*)
(*TODO: fix this for nodes and edges - probability of invalid nodes should be 0 *)
let uniform_distribution symbolic_start symbolic_end ty (g : AdjGraph.t) :
    float Cudd.Mtbdd.unique Cudd.Vdd.t =
  let prob = Mtbdd.cst B.mgr B.tbl_probabilities (uniform_probability_ty ty g) in
  prob

(* Given a type creates a BDD representing all possible values of that type*)
let create_value (ty : ty) (g : AdjGraph.t) : 'a t =
  let rec aux ty =
    let typ = get_inner_type ty in
    let symbolic_start, symbolic_end, res = B.freshvars typ in
    let distr = uniform_distribution symbolic_start symbolic_end typ g in
    B.push_symbolic_vars (symbolic_start, symbolic_end, typ, distr);
    match typ.typ with
    | TBool -> BBool res.(0)
    | TInt _ -> BInt res
    | TNode -> BInt res
    | TEdge -> failwith "todo once we introduce tuples?" (*aux i (TTuple [TNode; TNode]) *)
    (* | TTuple ts ->
        let bs, idx =
          List.fold_left
            (fun (ls, idx) t ->
              let v, i = aux idx t in
              (v :: ls, i))
            ([], i) ts
        in
        (Tuple (List.rev bs), idx) *)
    (* | TRecord map -> aux i (TTuple (RecordUtils.get_record_entries map))
       | TOption ty ->
           let v, idx = aux (i + 1) ty in
           (BOption (B.ithvar i, v), idx) *)
    | TArrow _ | QVar _ | TVar _ ->
        failwith
          (Printf.sprintf "internal error (create_value) type:%s\n"
             (Printing.ty_to_string (get_inner_type ty)))
  in
  aux ty

let create_value (ty_id : int) g : 'a t = create_value (TypeIds.get_elt type_store ty_id) g
