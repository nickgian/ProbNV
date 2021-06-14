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
  | TArrow _ | TVar _ | QVar _ | TMap _ | TRecord _ | TFloat ->
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

(* let vars_to_int size vars =
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
  aux 0 vars (Integer.create ~value:0 ~size) *)

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

(* Convert a list of BDD variables to an NV value based on the given type *)
let vars_to_svalue (vars, ty) =
  match ty.typ with
  | TBool ->
      let b = List.hd vars in
      if b = Man.Top then SBool FullSet else SBool (Subset (tbool_to_bool b))
  | TInt size ->
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SInt (Subset (vars_to_int size vars))
        (* let vars_expanded = expand vars 5 in
           SInt (Some (List.map (fun vars -> vars_to_int size vars) vars_expanded)) *)
      else SInt FullSet
  | TNode ->
      (* Was encoded as int, so decode same way *)
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SNode (Subset (List.map Integer.to_int (vars_to_int !tnode_sz vars)))
      else SNode FullSet
  | TEdge ->
      if List.exists (fun p -> not (p = Man.Top)) vars then
        SEdge
          (Subset
             (List.map
                (fun v ->
                  let e = Integer.to_int @@ v in
                  let u, v = PrimitiveCollections.IntMap.find e !edge_mapping in
                  (* Printf.printf "%d = (%d, %d)\n" e u v; *)
                  (u, v))
                (vars_to_int !tedge_sz vars)))
      else SEdge FullSet
  | TOption _ | TTuple _ | TRecord _ | TArrow _ | TMap _ | TVar _ | QVar _
  | TFloat ->
      failwith "internal error (unsupported types for symbolics)"

(* For debugging purposes *)
let rec printMtbdd distr =
  match Mtbddc.inspect distr with
  | Leaf _ -> Printf.printf "Leaf: %f\n" (Mtbddc.dval distr)
  | Ite (i, t, e) ->
      Printf.printf "top: %d: \n" i;
      Printf.printf "  dthen: ";
      printMtbdd t;
      Printf.printf "  delse: ";
      printMtbdd e

let printMtbdd printLeaf g =
  let rec aux g depth =
    match Mtbddc.inspect g with
    | Leaf v -> Printf.printf "Leaf: %s\n" (printLeaf (Mtbddc.get v))
    | Ite (i, t, e) ->
        Printf.printf "Var: %d: \n" i;
        Printf.printf "%s" (depth ^ "dthen: ");
        aux t (depth ^ "  ");
        Printf.printf "%s" (depth ^ "delse: ");
        aux e (depth ^ "  ")
  in
  aux g "  "

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

let printCube cube =
  Array.iter
    (fun v ->
      if v = Man.True then Printf.printf "1"
      else if v = Man.False then Printf.printf "0"
      else Printf.printf "*")
    cube

(* Memoizing vars_to_value *)
let vars_to_svalue =
  let tbl = Hashtbl.create 10000 in
  fun x ->
    try Hashtbl.find tbl x
    with Not_found ->
      let res = vars_to_svalue x in
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
      (* Printf.printf "%s:" name;
         List.iter
           (fun b ->
             match b with
             | Man.Top -> Printf.printf "*"
             | Man.True -> Printf.printf "1"
             | Man.False -> Printf.printf "0")
           subCube;
         Printf.printf ","; *)
      (* let subCube = Array.sub arr start (fin - start) |> Array.to_list in *)
      (name, vars_to_svalue (subCube, ty)) :: splitCube arr bounds

(* Given an assertion returns an assignment to symbolics that generated a counter-example (false property) *)
let rec generateSat (assertion : Cudd.Man.v Cudd.Bdd.t) bounds =
  let cubes = ref [] in
  (* NOTE: iter_cube might be a bit slow *)
  Bdd.iter_cube
    (fun arr ->
      (* printCube arr; *)
      (* Printf.printf "\n"; *)
      let cube = splitCube arr bounds in
      cubes := cube :: !cubes)
    assertion;
  !cubes

type symbolicAssignment = (Man.tbool list * ty) Collections.StringMap.t

type symbolicAssignments = symbolicAssignment list

(* Memoization for mutually recursive functions *)
let memoize2 () =
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

let mapAppend f1 f2 ls1 ls2 =
  let rec map f xs acc =
    match xs with [] -> acc | x :: xs -> map f xs (x :: acc)
  in
  map f2 ls2 (map f1 ls1 [])

let concat_map f l =
  let rec aux f acc = function
    | [] -> List.rev acc
    | x :: l ->
        let xs = f x in
        aux f (List.rev_append xs acc) l
  in
  aux f [] l

let generateAllSymbolicsMemoized :
    ((Cudd.Man.tbool list * ProbNv_lang.Syntax.ty)
     ProbNv_lang.Collections.StringMap.t
     * Cudd.Man.v Cudd.Bdd.t ->
    symbolicAssignments)
    option
    ref =
  ref None

(* TODO: generateSatFast should compute a set of assignments to symbolic values. *)
let generateSatFast (phi : Cudd.Man.v Cudd.Bdd.t) bounds =
  (* Compute the assignments for the full BDD *)
  let generateAllSymbolics self generateOneSymbolic
      ((m, phi) : symbolicAssignment * Cudd.Man.v Cudd.Bdd.t) :
      symbolicAssignments =
    match Bdd.inspect phi with
    | Bool false -> []
    | Bool true -> [ m ]
    | Ite (i, _, _) ->
        let name, start_var, end_var, ty, _ = BatMap.Int.find i bounds in
        let assignments = generateOneSymbolic (phi, start_var, end_var) in
        concat_map
          (fun (cube, phi') ->
            self (Collections.StringMap.add name (cube, ty) m, phi'))
          assignments
  in

  (* probSymbolic computes the probability for a single symbolic in the BDD*)
  let generateOneSymbolic _ self (phi, start_var, end_var) :
      (Cudd.Man.tbool list * Cudd.Man.v Bdd.t) list =
    match Bdd.inspect phi with
    | Bool false ->
        []
        (* if phi is false then we don't care about the assignments that led to it *)
    | Bool true ->
        [ ([], phi) ] (*if it's true then the empty assignment led to it *)
    | Ite (i, t, e) ->
        (* if it's a variable at level i *)
        if i > end_var then
          (* If we have moved on to another symbolic then return an empty assignment and the next symbolic. *)
          [ ([], phi) ]
        else
          (* Recursively compute the true and false branch with i+1 as the next start_variable
             (we have covered up to i) *)
          let trueBranch = self (t, i + 1, end_var) in
          let falseBranch = self (e, i + 1, end_var) in

          (* Add i - start_var * in the beginning if we have skipped them *)
          let fillStart = BatList.init (i - start_var) (fun _ -> Man.Top) in

          (* fill the end if necessary. If the next node is an Ite node that does not belong to this symbolic
              then we need to fill variables [i+1, end]. Likewise if the next variable is a boolean true.
          *)
          let fillEnd phi' lst =
            match Bdd.inspect phi' with
            | Ite (j, _, _) ->
                if j > end_var then
                  BatList.init (end_var - i) (fun _ -> Man.Top) @ lst
                else lst
            | Bool _ ->
                (*bool false can't really happen*)
                if i < end_var then
                  BatList.init (end_var - i) (fun _ -> Man.Top) @ lst
                else lst
          in

          let trueNew =
            List.map
              (fun (tas, phi) ->
                (fillStart @ [ Man.True ] @ fillEnd t tas, phi))
              trueBranch
          in
          let falseNew =
            List.map
              (fun (tas, phi) ->
                (fillStart @ [ Man.False ] @ fillEnd e tas, phi))
              falseBranch
          in

          (* let combo =
               mapAppend
                 (fun (tas, phi) -> (fillStart @ (Man.True :: fillEnd tas), phi))
                 (fun (fas, phi) -> (fillStart @ (Man.False :: fillEnd fas), phi))
                 trueBranch falseBranch
             in *)
          let combo = falseNew @ trueNew in
          combo
  in
  let generateAllSymbolics =
    match !generateAllSymbolicsMemoized with
    | None ->
        let f = memoize2 () generateAllSymbolics generateOneSymbolic in
        generateAllSymbolicsMemoized := Some f;
        f
    | Some f -> f
  in
  generateAllSymbolics (Collections.StringMap.empty, phi)

let symbolicAssignmentsToSvalues sassgn =
  List.map
    (fun m -> Collections.StringMap.map (fun v -> vars_to_svalue v) m)
    sassgn

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

let createDistributionMap (bounds : symbolic_var list) =
  let m = ref BatMap.Int.empty in
  List.iter
    (fun (name, start, finish, ty, distr) ->
      for i = start to finish do
        m := BatMap.Int.add i (name, start, finish, ty, distr) !m
      done)
    bounds;
  !m

(* Computes 2^(i-j) *)
let cardinality i j = float_of_int @@ (1 lsl (i - j))

(* Checks whether recursion has finished with the decision nodes of the current
symbolic *)
let isNextSymbolic dd end_var =
  match Bdd.inspect dd with Bool _ -> false | Ite (i, _, _) -> i > end_var

let computeTrueProbMemoized : (Cudd.Man.v Cudd.Bdd.t -> float) option ref =
  ref None

(* Algorithm currently used to compute probability of an assertion being true *)
let computeTrueProbability (assertion : bool Cudd.Mtbddc.t) bounds distrs cond
    counterexample =
  (* Compute the probability of the full BDD *)
  let rec computeProb _ probSymbolic guard =
    match Bdd.inspect guard with
    | Bool false -> 0.0
    | Bool true -> 1.0
    | Ite (i, _, _) ->
        let _, start_var, end_var, _, distr = BatMap.Int.find i distrs in
        (* printMtbdd string_of_float distr; *)
        (* Printf.printf "computeProb: %d, %d\n%!" start_var end_var;
           if Man.level_of_var mgr i <> i then
             Printf.printf " WARNING %d != %d\n" (Man.level_of_var mgr i) i; *)
        probSymbolic (guard, start_var, end_var, distr)
  in
  (* probSymbolic computes the probability for a single symbolic in the BDD*)
  let rec probSymbolic computeProb self (guard, start_var, end_var, distr) =
    match Bdd.inspect guard with
    | Bool false ->
        (* Printf.printf "probSymbolic false\n%!"; *)
        0.0
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
            (* Printf.printf "probSymbolic Ite/Leaf: %d, %d, i:%d\n" start_var
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
            (* Printf.printf "probSymbolic Ite/Ite: %d, %d, i:%d, j:%d\n" start_var
               end_var i j; *)
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
  let computeProbMem =
    match !computeTrueProbMemoized with
    | None ->
        let f = memoize2 () computeProb probSymbolic in
        computeTrueProbMemoized := Some f;
        f
    | Some f -> f
  in
  match cond with
  | None ->
      let cprob = computeProbMem trueBdd in
      (* Printf.printf "Printing the assertion BDD\n";
         printBdd trueBdd;
         Printf.printf "%!"; *)
      ( cprob,
        if counterexample && cprob < 1.0 then
          symbolicAssignmentsToSvalues
          @@ generateSatFast (Bdd.dnot trueBdd) distrs
        else [] )
  | Some c ->
      let intersection = Bdd.dand trueBdd c in
      let intersectionProb = computeProbMem intersection in
      let cprob = computeProbMem c in
      (* Printf.printf "inter: %5f, %5f\n" intersection cprob; *)
      ( intersectionProb /. cprob,
        if counterexample && cprob < 1.0 then
          (* generateSat (Bdd.dand c (Bdd.dnot trueBdd)) bounds; *)
          symbolicAssignmentsToSvalues
          @@ generateSatFast (Bdd.dand c (Bdd.dnot trueBdd)) distrs
        else [] )

let get_statistics () = Man.print_info mgr
