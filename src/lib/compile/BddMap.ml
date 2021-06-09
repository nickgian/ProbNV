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
let mgr = BddUtils.mgr

(* let tbl = Obj.magic (Mtbddc.make_table ~hash:Hashtbl.hash ~equal:( = )) *)

let tbl = BddUtils.tbl

(* Number of variables for maps *)
let nvars = ref 0

(* Number of variables for symbolics - initially -1 until the first map is created*)
let svars = ref (-1)

let set_size sz =
  (* Map requires sz number of variables, there are currently num_vars *)
  let num_vars = !nvars in
  if num_vars < sz then (
    for _ = 1 to sz - num_vars do
      ignore (Bdd.newvar mgr)
    done;
    nvars := num_vars + (sz - num_vars);
    Man.group mgr !svars !nvars Man.MTR_FIXED;
    Man.group mgr 0 (!svars + !nvars) Man.MTR_FIXED;
    (* In this case, since the manager has less variables than necessary, the range
       of the map type is represented through the first variable up to the last.
       We start from !svars as we need to ignore variables used for symbolics *)
    (!svars, !svars + sz - 1) )
  else
    (* In this case the manager has enough variables allocated to represent the
       given type. According to ithvar we use variables starting from zero (!svars),
       hence the range for this map is also !svars + !svars + sz - 1*)
    (!svars, !svars + sz - 1)

let ithvar i =
  (* set_size (i + 1); *)
  Bdd.ithvar mgr (!svars + i)

(* Assumes that symbolics are created before maps *)
let create ~(key_ty_id : int) ~(val_ty_id : int) (vnat : 'v) : 'v t =
  (* Update the number of symbolics if not yet done *)
  if !svars = -1 then svars := Man.get_bddvar_nb mgr;
  let key_ty = TypeIds.get_elt type_store key_ty_id in
  let r = set_size (BddUtils.ty_to_size key_ty) in
  { bdd = Mtbddc.cst mgr tbl vnat; key_ty_id; val_ty_id; var_range = r }

(** * Functions for find *)
let rec default_value ty =
  match ty.typ with
  | TBool -> avalue (vbool false, Some ty, Span.default)
  | TInt size ->
      avalue (vint (Integer.create ~value:0 ~size), Some ty, Span.default)
  | TFloat -> avalue (vfloat 0.0, Some ty, Span.default)
  | TTuple ts ->
      avalue (vtuple (BatList.map default_value ts), Some ty, Span.default)
  | TOption _ -> avalue (voption None, Some ty, Span.default)
  | TNode -> avalue (vnode 0, Some ty, Span.default)
  | TEdge -> avalue (vedge 0, Some ty, Span.default)
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
        let sz = !tnode_sz in
        let i = Integer.create ~value:(Obj.magic v) ~size:sz in
        (mk_int i idx, idx + sz)
    | TEdge ->
        (* based on edge id *)
        let sz = !tedge_sz in
        let i = Integer.create ~value:(Obj.magic v) ~size:sz in
        (mk_int i idx, idx + sz)
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
    | TMap _ | TVar _ | QVar _ | TArrow _ | TRecord _ | TFloat ->
        failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux ty v 0 in
  bdd

(** Takes as input an OCaml map and an ocaml key and returns an ocaml value*)
let find record_fns (vmap : 'v t) (k : 'key) : 'v =
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

let printBdd g =
  let rec aux g depth =
    match Bdd.inspect g with
    | Bool b -> Printf.printf "Bool: %b\n" b
    | Ite (i, t, e) ->
        Printf.printf "Var: %d: \n" i;
        Printf.printf "%s" (depth ^ "dthen: ");
        aux t (depth ^ "  ");
        Printf.printf "%s" (depth ^ "delse: ");
        aux e (depth ^ "  ")
  in
  aux g "  "

(* Returns the number of NV values that point to a given leaf *)
let cardinality (vmap : 'v t) (v : 'v) =
  (* i is guaranteed to be within (start, end) by construction *)
  (* Printf.printf "Entering cardinality\n";
     flush_all (); *)
  let guard = Mtbddc.guard_of_leaf tbl vmap.bdd v in

  (* Printf.printf "Got guard of leaf\n";
     flush_all (); *)
  (* Printf.printf "start, end: %d, %d\n%!" (fst vmap.var_range)
       (snd vmap.var_range);
     flush_all ();
     printBdd guard; *)
  let rec aux (phi, start_var, end_var) =
    match Bdd.inspect phi with
    | Bool true ->
        let res = 1 lsl (end_var - (start_var - 1)) in
        (* Printf.printf "true leaf returning %d\n" res; *)
        res
    | Bool false ->
        (* Printf.printf "false leaf\n"; *)
        0
    | Ite (i, t, e) ->
        (* Printf.printf "i: %d\n" i; *)
        let trueRec = aux (t, i + 1, end_var) in
        let falseRec = aux (e, i + 1, end_var) in

        (* Multiply by 2^(i - start_var) the cardinality *)
        let fillStart = if i > start_var then 1 lsl (i - start_var) else 1 in
        fillStart * (trueRec + falseRec)
  in
  let res =
    float_of_int @@ aux (guard, fst vmap.var_range, snd vmap.var_range)
  in
  (* Printf.printf "res: %f\n" res; *)
  res

(** ** Map merge operation, operates on top of OCaml values*)

(* Merge cache, int represents the function/operation and unit is is the closure
(not type safe) *)
module HashMergeMap = BatMap.Make (struct
  type t = int * unit

  (*NOTE: unit here is a placeholder for the closure type which is a tuple of OCaml variables*)

  let compare = Pervasives.compare
end)

let merge_op_cache = Obj.magic @@ ref HashMergeMap.empty

(* NOTE: Currently vty1=vty2 and the type of the result is also vty1*)

(** [op_key] is a tuple of the id of the function used to perform the
   merge and a tuple that contains the values of the closure.*)
let merge (op_key : int * 'f) f (vmap1 : 'a t) (vmap2 : 'a t) =
  let g x y = f (Mtbddc.get x) (Mtbddc.get y) |> Mtbddc.unique tbl in
  (* if cfg.no_caching then
   *   {vmap1 with bdd = (Mapleaf.mapleaf2 g (fst vmap1.bdd) (fst vmap2.bdd), (snd vmap1.bdd))}
   *   else *)
  let op_key = Obj.magic op_key in
  let op =
    (* match HashMergeMap.Exceptionless.find op_key !merge_op_cache with
       | None -> *)
    (* let o = *)
    User.make_op2 ~memo:Cudd.Memo.Global ~commutative:false ~idempotent:false g
    (* in
           merge_op_cache := HashMergeMap.add op_key o !merge_op_cache;
           o
       | Some op -> op *)
  in
  { vmap1 with bdd = User.apply_op2 op vmap1.bdd vmap2.bdd }

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
