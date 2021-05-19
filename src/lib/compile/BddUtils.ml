open ProbNv_lang
open Syntax
open Cudd
open ProbNv_utils
open ProbNv_datastructures
open Batteries

type distribution = float Mtbddc.t

type symbolic_var = string * int * int * ProbNv_lang.Syntax.ty * distribution

let mgr = Man.make_v ()

let set_reordering reorder =
  match reorder with
  | None -> ()
  | Some i -> (
      Cudd.Man.set_next_autodyn mgr 10000000;
      match i with
      | 0 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW2
      | 1 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW2_CONV
      | 2 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW3
      | 3 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW3_CONV
      | 4 -> Cudd.Man.enable_autodyn mgr REORDER_WINDOW4
      | 5 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT
      | 6 -> Cudd.Man.enable_autodyn mgr REORDER_SIFT_CONVERGE
      | _ -> () )

let () = Cudd.Man.set_max_cache_hard mgr 134217728

let bdd_of_bool b = if b then Bdd.dtrue mgr else Bdd.dfalse mgr

let rec ty_to_size ty =
  match (get_inner_type ty).typ with
  | TBool -> 1
  | TInt n -> n
  | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TOption tyo -> 1 + ty_to_size tyo
  | TNode -> ty_to_size (concrete (TInt !tnode_sz)) (* Encode as int *)
  | TEdge -> ty_to_size (concrete (TInt !tedge_sz)) (*Encode as edge id *)
  | TArrow _ | TVar _ | QVar _ | TMap _ | TRecord _ ->
      failwith ("internal error (ty_to_size): " ^ Printing.ty_to_string ty)

(* A list of the range of BDD variables, the type and the distribution, of every symbolic *)
let vars_list : (string * int * int * Syntax.ty * distribution) list ref =
  ref []

let push_symbolic_vars (name, i, j, typ, distr) =
  vars_list := (name, i, j, typ, distr) :: !vars_list

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

(* Computes the probability of a cube happening - includes all symbolics. 
This is super slow but might be useful for debugging so I am keeping it around. *)
let rec cubeProbability (cube : Cudd.Man.tbool array)
    (bounds : (string * int * int * Syntax.ty * float Cudd.Mtbddc.t) list) =
  match bounds with
  | [] -> 1.0
  | (_, xstart, xend, _, xdistribution) :: bounds ->
      (* compute the probability for one variable *)
      (* printBdd xdistribution;
         flush_all(); *)
      let p = symbolicProbability cube xstart xend xdistribution in

      (* debugging code *)
      (* Printf.printf "range:(%d,%d) " xstart xend;
         Printf.printf "cube: ";
         printCube cube;
         Printf.printf " symbProb: %f\n" p; *)
      p *. cubeProbability cube bounds

let rec computeTrueProbabilityOld (assertion : bool Cudd.Mtbddc.t) bounds =
  let ptrue = ref 0.0 in
  Mtbddc.iter_cube
    (fun cube v ->
      if v then ptrue := !ptrue +. cubeProbability cube bounds else ())
    assertion;
  !ptrue

let memoize f =
  let tbl = Hashtbl.create 1000 in
  let rec g x =
    try Hashtbl.find tbl x
    with Not_found ->
      let res = f g x in
      Hashtbl.add tbl x res;
      res
  in
  g

(* This function will only work for boolean symbolics - Not used.*)
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
              let p = Mtbddc.get a in
              (p, p)
          | Ite (_, pt, pf) -> (Mtbddc.dval pt, Mtbddc.dval pf)
        in
        (ptrue *. self t) +. (pfalse *. self e)
  in
  let memoized_aux = memoize aux in
  memoized_aux trueBdd

let createDistributionMap (bounds : symbolic_var list) =
  let m = ref BatMap.Int.empty in
  List.iter
    (fun (_, start, finish, _, distr) ->
      for i = start to finish do
        m := BatMap.Int.add i (start, finish, distr) !m
      done)
    bounds;
  !m

(* Computes 2^(i-j) *)
let cardinality i j = float_of_int @@ (1 lsl (i - j))

(* Checks whether recursion has finished with the decision nodes of the current
symbolic *)
let isNextSymbolic dd end_var =
  match Bdd.inspect dd with Bool _ -> false | Ite (i, _, _) -> i > end_var

(* Memoization for mutually recursive functions *)
let memoize2 =
  let tbl1 = Hashtbl.create 2000 in
  let tbl2 = Hashtbl.create 2000 in
  fun f1 f2 ->
  let rec g1 x =
    try Hashtbl.find tbl1 x
    with Not_found ->
      let res = f1 g1 g2 x in
      Hashtbl.add tbl1 x res;
      res
  and g2 x =
    try Hashtbl.find tbl2 x
    with Not_found ->
      let res = f2 g1 g2 x in
      Hashtbl.add tbl2 x res;
      res
  in
  g1

(* Algorithm currently used to compute probability of an assertion being true *)
let computeTrueProbability (assertion : bool Cudd.Mtbddc.t) distrs cond =
  (* Compute the probability of the full BDD *)
  let rec computeProb _ probSymbolic guard =
    match Bdd.inspect guard with
    | Bool false -> 0.0
    | Bool true -> 1.0
    | Ite (i, _, _) ->
        let start_var, end_var, distr = BatMap.Int.find i distrs in
        (* Printf.printf "computeProb: %d, %d\n%!" start_var end_var;
           if Man.level_of_var mgr i <> i then
             Printf.printf " WARNING %d != %d\n" (Man.level_of_var mgr i) i; *)
        probSymbolic (guard, start_var, end_var, distr)
  in
  (* probSymbolic computes the probability for a single symbolic in the BDD*)
  let rec probSymbolic computeProb self (guard, start_var, end_var, distr) =
    match Bdd.inspect guard with
    | Bool false -> 0.0
    | Bool true -> (
        match Mtbddc.inspect distr with
        | Leaf p ->
            (* If the distribution is at a leaf and the guard has reached a true leaf
               then the probability is the one given by the distribution multiplied by
               the number of integers described: i.e. 2^(end_var - start_var + 1)).
            *)
            (* Printf.printf "probSymbolic Bool true/Leaf p: %d, %d\n" start_var
               end_var; *)
            if end_var - (start_var - 1) > 0 then
              Mtbddc.get p *. cardinality end_var (start_var - 1)
            else Mtbddc.get p
        | Ite (j, td, ed) ->
            (* If the distribution is still not concrete then we recursively
               descend on it. we multiple by the number of integers we have covered
               until this point, i.e. 2^(j - start_var). Recursion restarts at j+1 *)
            (* Printf.printf "probSymbolic Bool true/Ite: %d, %d, j:%d\n" start_var
               end_var j; *)
            let space = cardinality j start_var in
            space
            *. ( self (guard, j + 1, end_var, td)
               +. self (guard, j + 1, end_var, ed) ) )
    | Ite (i, t, e) -> (
        match Mtbddc.inspect distr with
        | Leaf p ->
            (* In case the distribution is at a leaf, we need to be careful when
               recursing further. There are two cases: Either we are still recursing
               on the same symbolic or we have reached the next one (i.e., i > end_var). If we
               are on the next one, then we should call computeProb on that symbolic to recursively
               compute its probability and then multiply
               that result with the probability of the existing symbolic, i.e. p
               * cardinality (end-start+1) just like in the Bool/leaf case.
            *)
            (* Printf.printf "probSymbolic Bool Ite/Leaf: %d, %d, i:%d\n" start_var
               end_var i; *)
            if i > end_var then
              computeProb guard
              *.
              if end_var - start_var + 1 > 0 then
                Mtbddc.get p *. cardinality end_var (start_var - 1)
              else Mtbddc.get p
            else
              let space = cardinality i start_var in
              let rec_true = self (t, i + 1, end_var, distr) in
              let rec_false = self (e, i + 1, end_var, distr) in
              space *. (rec_true +. rec_false)
        | Ite (j, td, ed) ->
            (* Printf.printf "probSymbolic Bool Ite/Ite: %d, %d, i:%d, j:%d\n%!"
               start_var end_var i j; *)
            if i = j then
              (* Step both the distribution and the guard. We fork at this point and continue recursively *)
              cardinality i start_var
              *. (self (t, i + 1, end_var, td) +. self (e, i + 1, end_var, ed))
            else if i > j then
              (* Need to move the distribution. We fork at point j, and hence the start var for the recursion is j+1 *)
              cardinality j start_var
              *. ( self (guard, j + 1, end_var, td)
                 +. self (guard, j + 1, end_var, ed) )
            else
              (* if j > i, we move the guard, hence the new start_var is i+1. *)
              cardinality i start_var
              *. ( self (t, i + 1, end_var, distr)
                 +. self (e, i + 1, end_var, distr) ) )
  in
  let trueBdd = Mtbddc.guard_of_leaf tbl assertion true in
  let computeProbMem = memoize2 computeProb probSymbolic in
  match cond with
  | None -> computeProbMem trueBdd
  | Some c ->
      let intersection = Bdd.dand trueBdd c in
      let intersectionProb = computeProbMem intersection in
      let cprob = computeProbMem c in
      (* Printf.printf "inter: %5f, %5f\n" intersection cprob; *)
      intersectionProb /. cprob

let get_statistics () = Man.print_info mgr

let createTypeMap (bounds : (int * int * Syntax.ty * distribution) list) =
  let m = ref BatMap.Int.empty in
  List.iter
    (fun (start, finish, typ, _) ->
      for i = start to finish do
        m := BatMap.Int.add i (start, finish, typ) !m
      done)
    bounds;
  !m

type svalue =
  | SBool of Man.tbool (* Booleans are either true, false, or "Top" *)
  | SInt of Integer.t list option
  | SNode of node list option
  | SEdge of (node * node) list option

let rec expand (vars : Man.tbool list) sz : Man.tbool list list =
  if sz = 0 then [ vars ]
  else
    match vars with
    | [] -> [ [] ]
    | Man.Top :: xs ->
        let vars = expand xs (sz - 1) in
        let trus = List.map (fun v -> Man.False :: v) vars in
        let fals = List.map (fun v -> Man.True :: v) vars in
        fals @ trus
    | x :: xs ->
        let vars = expand xs sz in
        List.map (fun v -> x :: v) vars

let tbool_to_bool tb =
  match tb with Man.Top | Man.False -> false | Man.True -> true

let vars_to_int size vars =
  let rec aux i vars acc =
    match vars with
    | [] -> acc
    | v :: vars ->
        let bit = tbool_to_bool v in
        if bit then
          aux (i + 1) vars
            (Integer.add
               (Integer.shift_left (Integer.create ~value:1 ~size) i)
               acc)
        else aux (i + 1) vars acc
  in
  aux 0 vars (Integer.create ~value:0 ~size)

let vars_to_int size (vars : Man.tbool list) =
  let rec aux i vars =
    match vars with
    | [] -> [ Integer.create ~value:0 ~size ]
    | v :: vars -> (
        let rest = aux (i + 1) vars in
        match v with
        | Man.Top ->
            let x = Integer.shift_left (Integer.create ~value:1 ~size) i in
            let trus = List.map (fun v -> Integer.add x v) rest in
            rest @ trus
        | Man.True ->
            let rest = aux (i + 1) vars in
            let x = Integer.shift_left (Integer.create ~value:1 ~size) i in
            List.map (fun v -> Integer.add x v) rest
        | Man.False -> aux (i + 1) vars )
  in
  aux 0 vars

let vars_to_value (vars, ty) =
  match ty.typ with
  | TBool -> SBool (List.hd vars)
  | TInt size ->
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SInt (Some (vars_to_int size vars))
        (* let vars_expanded = expand vars 5 in
           SInt (Some (List.map (fun vars -> vars_to_int size vars) vars_expanded)) *)
      else SInt None
  | TNode ->
      (* Was encoded as int, so decode same way *)
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SNode (Some (List.map Integer.to_int (vars_to_int !tnode_sz vars)))
        (* let vars_expanded = expand vars 5 in
           SNode
             (Some
                (List.map
                   (fun vars -> Integer.to_int @@ vars_to_int !tnode_sz vars)
                   vars_expanded)) *)
      else SNode None
  | TEdge ->
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SEdge
          (Some
             (List.map
                (fun v ->
                  let e = Integer.to_int @@ v in
                  let u, v = PrimitiveCollections.IntMap.find e !edge_mapping in
                  Printf.printf "%d = (%d, %d)\n" e u v;
                  (u, v))
                (vars_to_int !tedge_sz vars)))
        (* let vars_expanded = expand vars 5 in *)
        (* SEdge
           (Some
              (List.map
                 (fun vars ->
                   let e = Integer.to_int @@ vars_to_int !tedge_sz vars in
                   let u, v = PrimitiveCollections.IntMap.find e !edge_mapping in
                   (* Printf.printf "%d = (%d, %d)\n" e u v; *)
                   (u, v))
                 vars_expanded)) *)
      else SEdge None
  | TOption _ | TTuple _ | TRecord _ | TArrow _ | TMap _ | TVar _ | QVar _ ->
      failwith "internal error (unsupported types for symbolics)"

let vars_to_value =
  let tbl = Hashtbl.create 10000 in
  fun x ->
    try Hashtbl.find tbl x
    with Not_found ->
      let res = vars_to_value x in
      Hashtbl.add tbl x res;
      res

let arrSubList arr start fin =
  let rec aux arr i fin =
    if i > fin then [] else arr.(i) :: aux arr (i + 1) fin
  in
  aux arr start fin

let rec splitCube arr bounds =
  match bounds with
  | [] -> []
  | (name, start, fin, ty, _) :: bounds ->
      let subCube = arrSubList arr start fin in
      (* let subCube = Array.sub arr start (fin - start) |> Array.to_list in *)
      (name, vars_to_value (subCube, ty)) :: splitCube arr bounds

(* Function that returns assignment to symbolics that generated a counter-example *)
let rec generateSat (assertion : bool Cudd.Mtbddc.t) bounds =
  let guard_f = Mtbddc.guard_of_leaf_u assertion (Mtbddc.unique tbl false) in
  let cubes = ref [] in
  Bdd.iter_cube
    (fun arr ->
      (* printCube arr;
         Printf.printf "\n"; *)
      let cube = splitCube arr bounds in
      cubes := cube :: !cubes)
    guard_f

(* Same algorithm as before but not memoized and with debug messages *)
(*let computeTrueProbability (assertion : bool Cudd.Mtbddc.t) bounds =
  let distrs = create_symbolics_map bounds in
  (* Compute the probability of the full BDD *)
  let rec computeProb guard =
    match Bdd.inspect guard with
    | Bool false ->
        (* Printf.printf "computeProb false\n%!"; *)
        0.0
    | Bool true ->
        (* Printf.printf "computeProb true\n%!"; *)
        1.0
    | Ite (i, _, _) ->
        let start_var, end_var, distr = BatMap.Int.find i distrs in
        (* Printf.printf "computeProb Ite: %d, %d\n%!" start_var end_var; *)
        probSymbolic (guard, start_var, end_var, distr)
  and probSymbolic (guard, start_var, end_var, distr) =
    match Bdd.inspect guard with
    | Bool false ->
        (* Printf.printf "probSymbolic Bool false: %d, %d\n" start_var end_var; *)
        0.0
    | Bool true -> (
        (* Printf.printf "probSymbolic Bool true: %d, %d\n" start_var end_var; *)
        match Mtbddc.inspect distr with
        | Leaf p ->
            (* If the distribution is at a leaf and the guard has reached a true leaf
               then the probability is the one given by the distribution multiplied by
               the number of integers left in the space of the symbolic: i.e. 2^(end_var - start_var) *)
            (* Printf.printf "probSymbolic Bool true/Leaf %f: %d, %d\n%!"
               (Mtbddc.get p) start_var end_var; *)
            let res =
              if end_var - start_var > 0 then
                Mtbddc.get p *. cardinality end_var start_var
              else Mtbddc.get p
            in
            (* Printf.printf "computed probability: %f\n%!" res; *)
            res
        | Ite (j, td, ed) ->
            (* If the distribution is still not concrete then we recursively
               descend on it. we multiple by the number of integers we have covered
               until this point, i.e. 2^(j - start_var). Recursion restarts at j *)
            let space = cardinality j start_var in
            (* Printf.printf "probSymbolic Bool true/Ite: %d, %d, j:%d\n%!"
               start_var end_var j; *)
            space
            *. ( probSymbolic (guard, j + 1, end_var, td)
               +. probSymbolic (guard, j + 1, end_var, ed) ) )
    | Ite (i, t, e) -> (
        match Mtbddc.inspect distr with
        | Leaf p ->
            (* In case the distribution is at a leaf, we need to be careful with
               the recursion. There are two cases: Either we are still recursing
               on the same symbolic or we are recursing on the next one. If we
               are recurring on the next one, call computeProb to recursively
               compute the probability of the next symbolics and then multiple
               that result with the probability of the existing symbolic, i.e. p
               * cardinality (end-i) just like in the Bool/leaf case.
            *)
            (* Printf.printf "probSymbolic Bool Ite/Leaf %f: %d, %d, i:%d\n%!"
               (Mtbddc.get p) start_var end_var i; *)
            if i > end_var then
              computeProb guard
              *.
              if end_var - (start_var - 1) > 0 then
                Mtbddc.get p *. cardinality end_var (start_var - 1)
              else Mtbddc.get p
            else
              let space = cardinality i start_var in
              let rec_true =
                (* if isNextSymbolic t end_var then
                     computeProb t *. Mtbddc.get p *. cardinality end_var i
                   else *)
                probSymbolic (t, i + 1, end_var, distr)
              in
              let rec_false =
                (* if isNextSymbolic e end_var then
                     computeProb e *. Mtbddc.get p *. cardinality end_var i
                   else *)
                probSymbolic (e, i + 1, end_var, distr)
              in
              space *. (rec_true +. rec_false)
        | Ite (j, td, ed) ->
            (* Printf.printf "probSymbolic Bool Ite/Ite: %d, %d, i:%d, j:%d\n%!"
               start_var end_var i j; *)
            if i = j then
              (* Step both the distribution and the guard. We fork at this point and continue recursively *)
              cardinality i start_var
              *. ( probSymbolic (t, i + 1, end_var, td)
                 +. probSymbolic (e, i + 1, end_var, ed) )
            else if i > j then
              (* Need to move the distribution. We fork at point j, and hence the start var for the recursion is j+1 *)
              cardinality j start_var
              *. ( probSymbolic (guard, j + 1, end_var, td)
                 +. probSymbolic (guard, j + 1, end_var, ed) )
            else
              (* if j > i, we move the guard, hence the new start_var is i+1. *)
              cardinality i start_var
              *. ( probSymbolic (t, i + 1, end_var, distr)
                 +. probSymbolic (e, i + 1, end_var, distr) ) )
  in
  let trueBdd = Mtbddc.guard_of_leaf tbl assertion true in
  computeProb trueBdd*)
