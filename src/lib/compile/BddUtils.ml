open ProbNv_lang
open Syntax
open Cudd
open ProbNv_utils
open ProbNv_datastructures
open Batteries

type distribution = float Mtbddc.t

let mgr = Man.make_v ()

let set_reordering reorder = 
  match reorder with
  | None -> ()
  | Some i ->
    (match i with
      | 0 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW2
      | 1 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW2_CONV
      | 2 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW3
      | 3 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW3_CONV
      | 4 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW4
      | 5 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT
      | 6 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT_CONVERGE
      | _ -> ())

(* let set_reordering reorder = 
  match reorder with
  | None -> ()
  | Some i ->
    (match i with
      | 0 -> Man.reduce_heap mgr REORDER_WINDOW2 1 
      | 1 -> Man.reduce_heap mgr REORDER_WINDOW2_CONV 1 
      | 2 -> Man.reduce_heap mgr REORDER_WINDOW3 1 
      | 3 -> Man.reduce_heap mgr  REORDER_WINDOW3_CONV 1
      (* | 4 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW4
      | 5 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT
      | 6 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT_CONVERGE *)
      | _ -> ()) *)

let () = Cudd.Man.set_max_cache_hard mgr 134217728

let bdd_of_bool b = if b then Bdd.dtrue mgr else Bdd.dfalse mgr

let rec ty_to_size ty =
  match (get_inner_type ty).typ with
  | TBool -> 1
  | TInt n -> n
  | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TOption tyo -> 1 + ty_to_size tyo
  (*
      | TRecord tmap -> ty_to_size (TTuple (RecordUtils.get_record_entries tmap)) *)
  | TNode -> ty_to_size (concrete (TInt tnode_sz)) (* Encode as int *)
  | TEdge -> 2 * ty_to_size (concrete TNode) (*Encode as node pair*)
  | TArrow _ | TVar _ | QVar _ | TMap _ | TRecord _ ->
      failwith ("internal error (ty_to_size): " ^ Printing.ty_to_string ty)

(* A list of the range of BDD variables, the type and the distribution, of every symbolic *)
let vars_list : (int * int * Syntax.ty * distribution) list ref = ref []

let push_symbolic_vars v = vars_list := v :: !vars_list

let freshvars ty =
  let symbolic_start = Man.get_bddvar_nb mgr in
  let sz = ty_to_size ty in
  let symbolic_end = symbolic_start + sz - 1 in
  let res = Array.init sz (fun _ -> Bdd.newvar mgr) in
  (symbolic_start, symbolic_end, res)

let freshvar () = Bdd.newvar mgr

let getVarsNb () = Man.get_bddvar_nb mgr

let tbl = Obj.magic (Mtbddc.make_table ~hash:Hashtbl.hash ~equal:( = ))

let tbl_probabilities : float Mtbddc.table =
  Mtbddc.make_table ~hash:Hashtbl.hash ~equal:( = )

let tbl_nv =
  Mtbddc.make_table
    ~hash:(hash_value ~hash_meta:false)
    ~equal:(equal_values ~cmp_meta:false)

(* let tbl_bool = Mtbddc.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = ) *)

let tbool_to_bool tb =
  match tb with Man.False | Man.Top -> false | Man.True -> true

let tbool_to_obool tb =
  match tb with
  | Man.False -> Some false
  | Man.Top -> None
  | Man.True -> Some true

(* Treats Top as false *)
(* let vars_to_value vars ty =
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
  fst (aux 0 ty) *)

(** * Probability computation functions *)

(* Moves through the distribution diagram towards a leaf *)
let move v distr =
  if v = Man.True then (*Move left or right *)
    Mtbddc.dthen distr
  else Mtbddc.delse distr

(* Counts the number of Top in cube from i to sz.*)
let count_tops cube i sz =
  let count = ref 0 in
  for k = i to sz do
    if cube.(k) = Man.Top then incr count
  done;
  !count

(* Computes the probability of a slice of a cube - only for a single symbolic *)
let rec symbolicProbability cube i j distr =
  (* Optimization: if we have reached a uniform distribution, just count tops. *)
  if Mtbddc.is_cst distr then
    float (1 lsl count_tops cube i j) *. Mtbddc.dval distr
  else if
    (* If we have examined all variables of this symbolic the distribution must be a leaf*)
    i > j
  then Mtbddc.dval distr
  else if
    (*If this variable is determined, then procceed down the appropriate path.
      Also move the distribution if necessary.*)
    cube.(i) = Man.True || cube.(i) = Man.False
  then
    symbolicProbability cube (i + 1) j
      (if Mtbddc.topvar distr = i then move cube.(i) distr else distr)
  else if
    (* Otherwise it's Top, and it can be both true and false.*)
    (not (Mtbddc.is_cst distr)) && Mtbddc.topvar distr = i
  then
    (*If the top variable in the distribution matches the given variable, then recurse on both cases, and move the distribution accordingly. *)
    symbolicProbability cube (i + 1) j (move Man.True distr)
    +. symbolicProbability cube (i + 1) j (move Man.False distr)
  else
    (* If the distribution does not depend on this variable we can optimize and compute only one branch*)
    2.0 *. symbolicProbability cube (i + 1) j distr

let printCube cube =
  Array.iter
    (fun v ->
      if v = Man.True then Printf.printf "1"
      else if v = Man.False then Printf.printf "0"
      else Printf.printf "*")
    cube

(* For debugging purposes *)
let rec printBdd distr =
  match Mtbddc.inspect distr with
  | Leaf _ -> Printf.printf "Leaf: %f\n" (Mtbddc.dval distr)
  | Ite (i, t, e) ->
      Printf.printf "top: %d: \n" i;
      Printf.printf "  dthen: ";
      printBdd t;
      Printf.printf "  delse: ";
      printBdd e

(* Computes the probability of a cube happening - includes all symbolics *)
let rec cubeProbability (cube : Cudd.Man.tbool array)
    (bounds : (int * int * Syntax.ty * float Cudd.Mtbddc.t) list) =
  match bounds with
  | [] -> 1.0
  | (xstart, xend, _, xdistribution) :: bounds ->
      (* compute the probability for one variable *)
      (* printBdd xdistribution;
      flush_all(); *)
      let p = symbolicProbability cube xstart xend xdistribution in
      (* debugging code *)
      (* Printf.printf "range:(%d,%d) " xstart xend;
         (* Printf.printf "cube: ";
         printCube cube; *)
         Printf.printf " symbProb: %f\n" p; *)

      p *. cubeProbability cube bounds

let rec computeTrueProbability (assertion : bool Cudd.Mtbddc.t) bounds =
  let ptrue = ref 0.0 in
  Mtbddc.iter_cube
    (fun cube v ->
      if v then ptrue := !ptrue +. cubeProbability cube bounds else ())
    assertion;
  !ptrue

  let memoize =
    let tbl = Hashtbl.create 1000 in
    fun f -> 
    let rec g x =
      try
        Hashtbl.find tbl x
      with
      Not_found ->
        let res = f g x in
          Hashtbl.add tbl x res;
          res
    in
      g

  (* This function will only work for boolean symbolics.
      In the future we might want to adapt it to any type of symbolics *)
  let computeTrueProbabilityBDD (assertion : bool Cudd.Mtbddc.t) distrs =
    let trueBdd = Mtbddc.guard_of_leaf tbl assertion true in
    let rec aux self guard =
      match Bdd.inspect guard with
      | Bool true -> 1.0
      | Bool false -> 0.0
      | Ite (i, t, e) ->
         let ptrue, pfalse = 
          match Mtbddc.inspect (BatMap.Int.find i distrs) with
          | Leaf a -> 
            let p = Mtbddc.get a in (p, p)
          | Ite(_, pt, pf) -> (Mtbddc.dval pt, Mtbddc.dval pf)
        in
          (ptrue *. self t) +. (pfalse *. self e)
    in
    let memoized_aux = memoize aux in
    memoized_aux trueBdd


(* let rec computeTrueProbabilityPar (assertion : bool Cudd.Mtbddc.t) bounds =
  let cubes = ref [] in
  Mtbddc.iter_cube
    (fun cube v ->
      if v then cubes := cube :: !cubes else ())
    assertion;
  parfold ~ncores:2 (fun cube acc -> acc +. (cubeProbability cube bounds)) (L !cubes) 0.0 (fun thread1 thread2 -> thread1 +. thread2)
    
let computeTrueProbability (assertion : bool Cudd.Mtbddc.t) bounds =
  computeTrueProbabilityPar assertion bounds *)


let get_statistics () = Man.print_info mgr
