open Batteries
open ProbNv_lang
open Syntax
open ProbNv_utils
open RecordUtils
open Collections
open OCamlUtils
open ProbNv_solution
open ProbNv_compile

let ty_transformer (recursors : Transformers.recursors) ty =
  match ty.typ with
  | TRecord map ->
      Some
        {
          ty with
          typ = TTuple (List.map recursors.recurse_ty (get_record_entries map));
        }
  | TVar { contents = Unbound _ } | QVar _ ->
      Some ty (* Allows record unrolling to be done before inlining *)
  | _ -> None

let pattern_transformer (recursors : Transformers.recursors) p ty =
  match (p, ty.typ) with
  | PRecord map, TRecord tmap ->
      Some
        (PTuple
           (List.map2 recursors.recurse_pattern (get_record_entries map)
              (get_record_entries tmap)))
  | _ -> None

let value_transformer (recursors : Transformers.recursors) v =
  match v.v with
  | VRecord map ->
      Some (vtuple (List.map recursors.recurse_value (get_record_entries map)))
  | _ -> None

let exp_transformer (rtys : ty StringMap.t list)
    (recursors : Transformers.recursors) e =
  match e.e with
  | ERecord map ->
      Some (etuple (List.map recursors.recurse_exp @@ get_record_entries map))
  | EProject (e1, l) ->
      let labels = get_type_with_label rtys failwith l |> get_record_labels in
      let index = List.index_of l labels |> oget in
      Some (eop (TGet (index, List.length labels)) [ recursors.recurse_exp e1 ])
  | _ -> None

let map_back_transformer recurse _ v orig_ty =
  match (v.v, orig_ty.typ) with
  | VTuple vs, TRecord tmap ->
      let vtys = get_record_entries tmap in
      let vlabels = get_record_labels tmap in
      let mapped_back_vs = List.map2 recurse vs vtys in
      let zipped = List.combine vlabels mapped_back_vs in
      Some
        (vrecord
           (List.fold_left
              (fun acc (l, v) -> StringMap.add l v acc)
              StringMap.empty zipped))
  | VTotalMap bdd, TMap (kty, vty) -> (
    (* Printf.printf "in total map/map case, before the crash\n with map type: %s" (Printing.ty_to_string orig_ty);
    flush_all(); *)
      match kty.typ with
      | TRecord _ as rty ->
          (* let op_key = (e_val v, BatSet.PSet.empty) in
          let record =
            BddMap.map op_key (fun v -> recurse v vty) bdd
            |> BddMap.change_key_type (Some { typ = rty; mode = kty.mode })
          in *)
          (* Printf.printf "made it out of the map/map\n";
          flush_all(); *)
          None
          (* Some (vmap record (Some orig_ty)) *)
      | _ -> 
      (* Printf.printf "made it out of the map/map\n";
      flush_all(); *)
      None )
  | VTotalMap (bdd, kty), TRecord _ ->
      (* case of multi-value record *)
      let g x =
        recurse (Cudd.Mtbddc.get x) orig_ty |> Cudd.Mtbddc.unique BddUtils.tbl_nv
      in
      let record = Cudd.Mapleaf.mapleaf1 g bdd in
      (* let record = BddMap.map op_key (fun v -> recurse v orig_ty) bdd in *)
      (* Printf.printf "never made it out\n";
      flush_all(); *)
      Some (vmap (record, kty) None)
  | _ -> None

let mask_transformer = map_back_transformer

(* Conveniently works in this case *)

let make_toplevel (rtys : ty StringMap.t list)
    (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer ~name:"RecordUnrolling" ty_transformer
    pattern_transformer value_transformer (exp_transformer rtys)
    map_back_transformer

let unroll_declarations decls =
  make_toplevel (get_record_types decls) Transformers.transform_declarations
    decls
