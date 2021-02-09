open ProbNv_lang
open Syntax
open Cudd
open ProbNv_utils
open ProbNv_datastructures
open Batteries
open Embeddings
open CompileBDDs
open Collections

(* Manager for total maps *)
let mgr = Man.make_v ()

(* let tbl = Obj.magic (Mtbddc.make_table ~hash:Hashtbl.hash ~equal:( = )) *)

let tbl = BddUtils.tbl

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for _ = 1 to sz - num_vars do
      ignore (Bdd.newvar mgr)
    done

let ithvar i =
  set_size (i + 1);
  Bdd.ithvar mgr i

let create ~(key_ty_id : int) ~(val_ty_id : int) (vnat : 'v) : 'v t =
  let key_ty = TypeIds.get_elt type_store key_ty_id in
  set_size (BddUtils.ty_to_size key_ty);
  { bdd = Mtbddc.cst mgr tbl vnat; key_ty_id; val_ty_id }

(** * Functions for find *)
let rec default_value ty =
  match ty.typ with
  | TBool -> avalue (vbool false, Some ty, Span.default)
  | TInt size ->
      avalue (vint (Integer.create ~value:0 ~size), Some ty, Span.default)
  | TTuple ts ->
      avalue (vtuple (BatList.map default_value ts), Some ty, Span.default)
  | TOption _ -> avalue (voption None, Some ty, Span.default)
  | TNode -> avalue (vnode 0, Some ty, Span.default)
  | TEdge -> avalue (vedge (0, 1), Some ty, Span.default)
  | TVar { contents = Link t } -> default_value t
  | TVar _ | QVar _ | TArrow _ | TMap _ | TRecord _ ->
      failwith "internal error (default_value)"

let get_bit (n : int) (i : int) : bool =
  let marker = Z.shift_left Z.one i in
  Z.logand (Z.of_int n) marker <> Z.zero

let mk_int i idx =
  let acc = ref (Bdd.dtrue mgr) in
  let sz = Integer.size i in
  let iz = Z.to_int (Integer.value i) in
  for j = 0 to sz - 1 do
    let var = ithvar (idx + j) in
    let bit = get_bit iz j in
    let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
    acc := Bdd.dand !acc (Bdd.eq var bdd)
  done;
  !acc

(** value_to_bdd converts an OCaml Value to a Bdd. It requires an NV type for the given OCaml value -
    used in map find *)
let value_to_bdd (record_fns : int * int -> 'a -> 'b) (ty : Syntax.ty) (v : 'v)
    : Bdd.vt =
  let rec aux ty v idx =
    match ty.typ with
    | TBool ->
        let var = ithvar idx in
        ((if Obj.magic v then var else Bdd.dnot var), idx + 1)
    | TInt sz ->
        let i = Integer.create ~value:(Obj.magic v) ~size:sz in
        (mk_int i idx, idx + sz)
    | TTuple ts ->
        let base = Bdd.dtrue mgr in
        let n = BatList.length ts in
        let proj_fun i = (i, n) in
        let proj_val i = record_fns (proj_fun i) in
        List.fold_lefti
          (fun (bdd_acc, idx) vindex ty ->
            let bdd, i = aux ty (Obj.magic (proj_val vindex v)) idx in
            (Bdd.dand bdd_acc bdd, i))
          (base, idx) ts
    | TNode ->
        (* Encode same way as we encode ints *)
        let sz = tnode_sz in
        let i = Integer.create ~value:(Obj.magic v) ~size:sz in
        (mk_int i idx, idx + sz)
    | TEdge ->
        let bdd1, i = aux (concrete TNode) (fst (Obj.magic v)) idx in
        let bdd2, i = aux (concrete TNode) (snd (Obj.magic v)) i in
        (Bdd.dand bdd1 bdd2, i)
    | TOption typ -> (
        match Obj.magic v with
        | None ->
            let var = ithvar idx in
            let tag = Bdd.eq var (Bdd.dfalse mgr) in
            let dv = default_value (ProbNv_utils.OCamlUtils.oget v.vty) in
            let value, idx = aux typ dv (idx + 1) in
            (Bdd.dand tag value, idx)
        | Some v ->
            let var = ithvar idx in
            let tag = Bdd.eq var (Bdd.dtrue mgr) in
            let value, idx = aux typ v (idx + 1) in
            (Bdd.dand tag value, idx) )
    | TMap _ | TVar _ | QVar _ | TArrow _ | TRecord _ ->
        failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux ty v 0 in
  bdd

(** Takes as input an OCaml map and an ocaml key and returns an ocaml value*)
let find record_fns (vmap : 'v t) (k : 'key) : 'v =
  (* print_endline "inside find\n"; *)
  let key_ty = TypeIds.get_elt type_store vmap.key_ty_id in
  let bdd = value_to_bdd record_fns key_ty k in
  let for_key = Mtbddc.constrain vmap.bdd bdd in
  Mtbddc.pick_leaf for_key

(** Update vmap at key k with value v *)
let update record_fns (vmap : 'v t) (k : 'key) (v : 'v) : 'v t =
  (* print_endline "inside update\n"; *)
  let key_ty = TypeIds.get_elt type_store vmap.key_ty_id in
  let key = value_to_bdd record_fns key_ty k in
  let leaf = Mtbddc.cst mgr tbl v in
  { vmap with bdd = Mtbddc.ite key leaf vmap.bdd }

module HashClosureMap = BatMap.Make (struct
  type t = int * unit

  (*NOTE: unit here is a placeholder for the closure type which is a tuple of OCaml variables*)

  let compare = Pervasives.compare
end)

(** * Used for inversing transformations only*)

module ExpMap = BatMap.Make (struct
  type t = exp * value BatSet.PSet.t

  let compare = Pervasives.compare
end)

let map_cache = ref ExpMap.empty

(** Operates on top of nv values *)
let map ~op_key (f : value -> value) ((vdd, ty) : Syntax.mtbdd) : Syntax.mtbdd =
  (* print_endline "inside map\n"; *)
  let g x = f (Mtbddc.get x) |> Mtbddc.unique B.tbl_nv in
  let op =
    match ExpMap.Exceptionless.find op_key !map_cache with
    | None ->
        let o =
          User.make_op1 ~memo:Cudd.Memo.Global
            (* ~memo:(Memo.Cache (Cache.create1 ~maxsize:4096 ())) *)
            g
        in
        map_cache := ExpMap.add op_key o !map_cache;
        o
    | Some op -> op
  in
  (User.apply_op1 op vdd, ty)

let change_key_type ty (map, _) = (map, ty)
