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

let tbl_bool = Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

(*Gets i-th bit of the integer n *)
let get_bit (n : int) (i : int) : bool =
  let marker = Z.shift_left Z.one i in
  Z.logand (Z.of_int n) marker <> Z.zero

(* let get_bit (n : Integer.t) (i : int) : bool =
  let z = Integer.value n in
  let marker = Z.shift_left Z.one i in
  Z.logand z marker <> Z.zero *)

let tbool_to_bool tb = match tb with Man.False | Man.Top -> false | Man.True -> true

let count_tops arr sz =
  let j = ref 0 in
  for i = 0 to sz - 1 do
    match arr.(i) with Man.Top -> incr j | _ -> ()
  done;
  !j

let rec expand (vars : Man.tbool list) sz : Man.tbool list list =
  if sz = 0 then [[]]
  else
    match vars with
    | [] -> [[]]
    | Man.Top :: xs ->
        let vars = expand xs (sz - 1) in
        let trus = List.map (fun v -> Man.False :: v) vars in
        let fals = List.map (fun v -> Man.True :: v) vars in
        fals @ trus
    | x :: xs ->
        let vars = expand xs (sz - 1) in
        List.map (fun v -> x :: v) vars

let tbool_to_obool tb =
  match tb with Man.False -> Some false | Man.Top -> None | Man.True -> Some true
