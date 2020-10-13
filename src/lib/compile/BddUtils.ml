open ProbNv_lang
open Syntax
open Cudd
open ProbNv_utils
open ProbNv_datastructures
open Batteries

let mgr = Man.make_v ()

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for _ = 1 to sz - num_vars do
      ignore (Bdd.newvar mgr)
    done

let ithvar i =
  set_size (i + 1);
  Bdd.ithvar mgr i

let rec ty_to_size ty =
  match (get_inner_type ty).typ with
  | TBool -> 1
  | TInt n -> n
  (* | TOption tyo -> 1 + ty_to_size tyo
     | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
     | TRecord tmap -> ty_to_size (TTuple (RecordUtils.get_record_entries tmap)) *)
  | TNode -> ty_to_size (concrete (TInt tnode_sz)) (* Encode as int *)
  (* | TEdge -> ty_to_size (TTuple [TNode; TNode]) (*Encode as node pair*) *)
  | TArrow _ | TVar _ | QVar _ ->
      failwith ("internal error (ty_to_size): " ^ Printing.ty_to_string ty)

let tbl = Obj.magic (Mtbdd.make_table ~hash:Hashtbl.hash ~equal:( = ))

let tbl_nv =
  Mtbdd.make_table
    ~hash:(hash_value ~hash_meta:false)
    ~equal:(equal_values ~cmp_meta:false)

(* let tbl_bool = Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = ) *)

(*Gets i-th bit of the integer n *)
let get_bit (n : int) (i : int) : bool =
  let marker = Z.shift_left Z.one i in
  Z.logand (Z.of_int n) marker <> Z.zero

(* let get_bit (n : Integer.t) (i : int) : bool =
  let z = Integer.value n in
  let marker = Z.shift_left Z.one i in
  Z.logand z marker <> Z.zero *)

let tbool_to_bool tb =
  match tb with Man.False | Man.Top -> false | Man.True -> true

let count_tops arr sz =
  let j = ref 0 in
  for i = 0 to sz - 1 do
    match arr.(i) with Man.Top -> incr j | _ -> ()
  done;
  !j

let rec expand (vars : Man.tbool list) sz : Man.tbool list list =
  if sz = 0 then [ [] ]
  else
    match vars with
    | [] -> [ [] ]
    | Man.Top :: xs ->
        let vars = expand xs (sz - 1) in
        let trus = List.map (fun v -> Man.False :: v) vars in
        let fals = List.map (fun v -> Man.True :: v) vars in
        fals @ trus
    | x :: xs ->
        let vars = expand xs (sz - 1) in
        List.map (fun v -> x :: v) vars

let tbool_to_obool tb =
  match tb with
  | Man.False -> Some false
  | Man.Top -> None
  | Man.True -> Some true

(* Treats Top as false *)
let vars_to_value vars ty =
  let open RecordUtils in
  let rec aux idx ty =
    let v, i =
      match (get_inner_type ty).typ with
      | TBool -> (vbool (tbool_to_bool vars.(idx)), idx + 1)
      | TInt size ->
          let acc = ref (Integer.create ~value:0 ~size) in
          for i = 0 to size - 1 do
            let bit = tbool_to_bool vars.(idx + i) in
            if bit then
              let add = Integer.shift_left (Integer.create ~value:1 ~size) i in
              acc := Integer.add !acc add
          done;
          (vint !acc, idx + size)
      (* | TTuple ts ->
         let vs, i =
           List.fold_left
             (fun (vs, idx) ty ->
               let v, i = aux idx ty in
               v :: vs, i)
             ([], idx)
             ts
         in
         vtuple (List.rev vs), i *)
      (* | TRecord map ->
         (* This will have been encoded as if it's a tuple.
            So get the tuple type and use that to decode *)
         let tup = TTuple (get_record_entries map) in
         let vals, i = aux idx tup in
         let vals =
           match vals with
           | { v = VTuple vs; _ } -> vs
           | _ -> failwith "impossible"
         in
         (* Reconstruct the record *)
         let open PrimitiveCollections in
         let recmap =
           List.fold_left2
             (fun acc l v -> StringMap.add l v acc)
             StringMap.empty
             (RecordUtils.get_record_labels map)
             vals
         in
         vrecord recmap, i *)
      | TNode -> (
          (* Was encoded as int, so decode same way *)
          match aux idx (concrete (TInt tnode_sz)) with
          | { v = VInt n; _ }, i -> (vnode (Integer.to_int n), i)
          | _ -> failwith "impossible" )
      (* | TEdge -> (
             (* Was encoded as tuple of nodes *)
             match aux idx (TTuple [ TNode; TNode ]) with
             | { v = VTuple [ { v = VNode n1; _ }; { v = VNode n2; _ } ]; _ }, i ->
                 (vedge (n1, n2), i)
             | _ -> failwith "impossible" )
         | TOption tyo ->
             let tag = B.tbool_to_bool vars.(idx) in
             let v, i = aux (idx + 1) tyo in
             let v = if tag then voption (Some v) else voption None in
             (v, i) *)
      | TArrow _ | TVar _ | QVar _ -> failwith "internal error (bdd_to_value)"
    in
    (* let ty =
         match ty with TRecord map -> TTuple (get_record_entries map) | _ -> ty
       in *)
    (annotv ty v, i)
  in
  fst (aux 0 ty)

let pick_default_value (map, ty) =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
      let c = count_tops vars (ty_to_size ty) in
      if c > !count then count := c;
      value := Some v)
    map;
  OCamlUtils.oget !value

(* Basic version *)
let bindings (map : mtbdd) : (value * value) list * value =
  let bs = ref [] in
  let dv = pick_default_value (map, ty) in
  Mtbdd.iter_cube
    (fun vars v ->
      let lst = Array.to_list vars in
      let sz = B.ty_to_size ty in
      let expanded =
        if B.count_tops vars sz <= 2 then B.expand lst sz else [ lst ]
      in
      List.iter
        (fun vars ->
          if not (equal_values ~cmp_meta:false v dv) then
            let k = vars_to_value (Array.of_list vars) ty in
            bs := (k, v) :: !bs)
        expanded)
    map;
  (!bs, dv)
