open ProbNv_lang
(** * OCaml to ProbNV Embeddings*)

open ProbNv_utils
open ProbNv_datastructures
open PrimitiveCollections
open Syntax
open CompileBDDs
open Cudd
module B = BddUtils

(** Given an NV type and an OCaml value constructs an NV value*)
let rec embed_value (record_fns : int * int -> 'a -> 'b) (typ : Syntax.ty) :
    'v -> Syntax.value =
  match typ.typ with
  | TBool -> fun v -> Syntax.vbool (Obj.magic v)
  | TInt n -> fun v -> Syntax.vint (Integer.create ~value:(Obj.magic v) ~size:n)
  | TTuple ts ->
      let n = BatList.length ts in
      let fs =
        BatList.mapi
          (fun i ty ->
            let proj_fun = (i, n) in
            let f_rec = embed_value record_fns ty in
            let proj_val = record_fns proj_fun in
            fun v ->
              let vrec = v in
              f_rec (Obj.magic (proj_val vrec)))
          ts
      in
      fun v -> Syntax.vtuple (BatList.map (fun f -> f v) fs)
  | TOption ty -> (
      let f = embed_value record_fns ty in
      fun v ->
        match Obj.magic v with
        | None -> Syntax.voption None
        | Some v' -> Syntax.voption (Some (f v')) )
  | TMap (kty, vty) ->
      let g x =
        embed_value record_fns vty (Mtbddc.get x) |> Mtbddc.unique B.tbl_nv
      in
      fun v ->
        let omap = Obj.magic v in
        let vbdd = Mapleaf.mapleaf1 g omap.bdd in
        Syntax.vmap (vbdd, Some (kty, omap.var_range)) (Some typ)
  | TArrow _ ->
      failwith
        (Printf.sprintf "Function %s computed as value"
           (Printing.ty_to_string typ))
  | TRecord _ -> failwith "Trecord"
  | TNode -> fun v -> Syntax.vnode (Obj.magic v)
  | TEdge -> fun v -> Syntax.vedge (Obj.magic v)
  | TVar { contents = Link ty } -> embed_value record_fns ty
  | TVar _ | QVar _ -> failwith "TVars and QVars should not show up here"

(** Takes an NV value of type typ and returns an OCaml value.*)
let rec unembed_value _ _ _ : Syntax.value -> 'v =
  failwith "this function is no longer necessary, remove it"

(* Lifts embed_value to a multivalue - We don't assign a key type here. *)
let embed_multivalue (record_fns : int * int -> 'a -> 'b) (typ : Syntax.ty) v =
  let g x =
    embed_value record_fns typ (Mtbddc.get x) |> Mtbddc.unique B.tbl_nv
  in
  Syntax.vmap (Mapleaf.mapleaf1 g (Obj.magic v), None) (Some typ)

(* Cache of embed functions based on type. The size here is an arbitrary number,
   the size of the type array is what is eventually used. *)
let embed_cache : (int * int -> int) array ref =
  ref (Array.create 100 (fun _ -> 0))

let build_embed_cache record_fns =
  embed_cache :=
    Array.map
      (fun ty -> Obj.magic (embed_value record_fns ty))
      (Collections.TypeIds.to_array type_store)

let unembed_cache : (int * int -> int) array ref =
  ref (Array.create 100 (fun _ -> 0))

let build_unembed_cache record_cnstrs record_fns =
  unembed_cache :=
    Array.map
      (fun ty -> Obj.magic (unembed_value record_cnstrs record_fns ty))
      (Collections.TypeIds.to_array type_store)

let embed_value_id ty_id (v : 'v) : Syntax.value =
  let embedding : 'v -> value = !embed_cache.(ty_id) |> Obj.magic in
  embedding v

let unembed_value_id ty_id (v : Syntax.value) : 'v =
  let unembedding : value -> 'v = !unembed_cache.(ty_id) |> Obj.magic in
  unembedding v
