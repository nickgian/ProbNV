open Cudd

(* BDD Manager *)
let mgr = Man.make_v ()

(* Leaf table *)
let tbl = Mtbdd.make_table ~hash:Hashtbl.hash ~equal:( = )

(* A table to represent BDDs as MTBDDs - might not be necessary *)
let tbl_bool = Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

(* tbl probabilities *)
let tbl_prob = Mtbdd.make_table ~hash:Hashtbl.hash ~equal:( = )

(* BDD to MTBDD *)
let wrap_mtbdd bdd =
  let tru = Mtbdd.cst mgr tbl_bool true in
  let fal = Mtbdd.cst mgr tbl_bool false in
  Mtbdd.ite bdd tru fal

(* BDD function <= *)
let leq xs ys =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let acc = ref (Bdd.dtrue mgr) in
  Array.iter2 (fun x y -> acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))) xs ys;
  !acc

let eq xs ys =
  let acc = ref (Bdd.dtrue mgr) in
  Array.iter2 (fun x y -> acc := Bdd.dand !acc (Bdd.eq x y)) xs ys;
  !acc

  let lt xs ys =
    match (leq xs ys, eq xs ys) with
    | b1, b2 ->
        let b = Bdd.dand b1 (Bdd.dnot b2) in
        b

let bdd_of_bool b = if b then Bdd.dtrue mgr else Bdd.dfalse mgr

 let get_bit (n : int) (i : int) : bool =
  let marker = Z.shift_left Z.one i in
  Z.logand (Z.of_int n) marker <> Z.zero

let mk_int n sz =
  Array.init sz (fun j ->
        let bit = get_bit n j in
        bdd_of_bool bit)  
  ;;

let x = Array.init 3 (fun _ -> Bdd.newvar mgr)

let space = 1./.6.0

let maxNum = mk_int 6 3;;

let isValid = lt x maxNum

let distrX = Mtbdd.ite isValid  (Mtbdd.cst mgr tbl_prob space) (Mtbdd.cst mgr tbl_prob 0.0) 

let rec printBdd distr =
  match Mtbdd.inspect distr with
  | Leaf _ -> Printf.printf "Leaf: %b\n" (Mtbdd.dval distr)
  | Ite (i, t, e) ->
      Printf.printf "top: %d: \n" i;
      Printf.printf "  dthen: ";
      printBdd t;
      Printf.printf "  delse: ";
      printBdd e

      let rec printBddB x =
        match Bdd.inspect x with
        | Bdd.Bool b -> Printf.printf "Leaf: %b\n" b
        | Bdd.Ite (i, t, e) ->
            Printf.printf "top: %d: \n" i;
            Printf.printf "  dthen: ";
            printBddB t;
            Printf.printf "  delse: ";
            printBddB e

(** Addition between bdds*)
let add xs ys =
  let var3 = ref (Bdd.dfalse mgr) in
  let var4 = Array.make (Array.length xs) (Bdd.dfalse mgr) in
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
  var4

(** * Probability functions *)

let move v var distr =
  if (not (Mtbdd.is_cst distr)) && Mtbdd.topvar distr = var then
    (*If the top variable in the distribution matches the given variable *)
    if v = Man.True then (*Move left or right *)
      Mtbdd.dthen distr else Mtbdd.delse distr
  else (*Otherwise nothing changes *)
    distr

(* Computes the probability of a slice of a cube - only for a single symbolic *)
let rec symbolicProbability cube i sz distr =
  (* TODO: Check here if distr is leaf and optimize *)
  if i > sz then Mtbdd.dval distr
    (* If we have examined all variables of this symbolic the distribution must be a leaf*)
  else if cube.(i) = Man.True || cube.(i) = Man.False then
    symbolicProbability cube (i + 1) sz (move cube.(i) i distr)
  else
    (*TODO: optimize *)
    symbolicProbability cube (i + 1) sz (move Man.True i distr)
    +. symbolicProbability cube (i + 1) sz (move Man.False i distr)

(* Computes the probability of a cube happening - includes all symbolics *)
let rec cubeProbability (cube : Cudd.Man.tbool array)
    (bounds : (int * int * float Cudd.Mtbdd.t) list) =
  match bounds with
  | [] -> 1.0
  | (xstart, xend, xdistribution) :: bounds ->
      let p = symbolicProbability cube xstart xend xdistribution in
      p *. cubeProbability cube bounds

let rec computeTrueProbability (assertion : bool Cudd.Mtbdd.t) bounds =
  let ptrue = ref 0.0 in
  Mtbdd.iter_cube
    (fun cube v -> if v then ptrue := !ptrue +. cubeProbability cube bounds else ())
    assertion;
  !ptrue

let bounds = ref []

let two = [|Bdd.dfalse mgr; Bdd.dtrue mgr|]

(* symbolic x with non-uniform distribution *)
let x_int2 =
  let nvars = Man.get_bddvar_nb mgr in
  let a1 = Bdd.newvar mgr in
  let a2 = Bdd.newvar mgr in
  let distr =
    Mtbdd.ite
      (leq [|a1; a2|] two)
      (Mtbdd.cst mgr tbl_prob (1.0 /. 3.0))
      (Mtbdd.cst mgr tbl_prob 0.0)
  in
  bounds := (nvars, nvars + 1, distr) :: !bounds;
  [|a1; a2|]

(* symbolic y *)
let y_int2 =
  let nvars = Man.get_bddvar_nb mgr in
  bounds := (nvars, nvars + 1, Mtbdd.cst mgr tbl_prob 0.25) :: !bounds;
  let a1 = Bdd.newvar mgr in
  let a2 = Bdd.newvar mgr in
  [|a1; a2|]

(** Let's model the function, if x>=2 then true else y>=2 *)

let xgttwo = leq two x_int2

let ygttwo = leq two y_int2

let asserted_function = Mtbdd.ite xgttwo (Mtbdd.cst mgr tbl_bool true) (wrap_mtbdd ygttwo)

let _ = bounds := List.rev !bounds

let prob = computeTrueProbability asserted_function !bounds

(* A "map", it does not depend on any symbolic right now, it's a leaf with value 0*)
let v = Mtbdd.cst mgr tbl 0

(* Creating a "symbolic", 4 bit-integer. *)
let symbx =
  let a1 = Bdd.newvar mgr in
  let a2 = Bdd.newvar mgr in
  let a3 = Bdd.newvar mgr in
  let a4 = Bdd.newvar mgr in
  [|a1; a2; a3; a4|]

let symby =
  let a1 = Bdd.newvar mgr in
  let a2 = Bdd.newvar mgr in
  let a3 = Bdd.newvar mgr in
  let a4 = Bdd.newvar mgr in
  [|a1; a2; a3; a4|]

let three = [|Bdd.dtrue mgr; Bdd.dtrue mgr; Bdd.dfalse mgr; Bdd.dfalse mgr|]

(* Set of 4-bit integers that are less or equal to three *)
let symbxLtThree = leq symbx three

let symbyEqThree = eq symby three

let binds m =
  let bs = ref [] in
  Mtbdd.iter_cube (fun vars v -> bs := (vars, v) :: !bs) m;
  !bs

let t_to_distr var_list leaf =
  let rec aux vars =
    match vars with
    | [] -> leaf
    | b :: vars ->
        let v = aux vars in
        Mtbdd.ite b v v
  in
  aux var_list

(* 4-bit uniform *)
let symbx_distr = t_to_distr (Array.to_list symbx) (Mtbdd.cst mgr tbl_prob (1.0 /. 16.0))

let symbx_distr_2 = Mtbdd.constrain (Mtbdd.cst mgr tbl_prob (1.0 /. 16.0)) (Array.fold_left ())

(* mapIf takes a predicate in the form a BDD (MTBDD with boolean leafs for library reasons, 
 * a function f from integers to integers
 * and v, a multi-terminal bdd with int leafs
 * and combines the predicate and the MTBDD by applying f over the leafs of v when the predicate is true. *)

(* An optimization (that will be good to do when possible) is implemented using the special argument.
 * If special bdd1 bdd2 = Some res then a full recursive descent is not required.
 * For mapIf, basically for paths of the predicate's tree which are constant and false, we don't need to visit the leafs of the MTBDD v, the result is v.
 *)

let g _ (arr : 'a Cudd.Mtbdd.unique Cudd.Vdd.t array) : 'a Cudd.Mtbdd.unique Cudd.Vdd.t option =
  if Mtbdd.is_cst arr.(0) && Mtbdd.is_cst arr.(1) && Mtbdd.is_cst arr.(2) then
    Some
      ( Obj.magic
          ( if Obj.magic (Mtbdd.dval arr.(0)) then snd (Obj.magic (Mtbdd.dval arr.(1)))
          else snd (Obj.magic (Mtbdd.dval arr.(2))) )
      |> Mtbdd.cst mgr tbl )
  else None

let op = User.make_opN ~memo:Cudd.(Cache (Cache.create 3)) 0 3 g

let v2 =
  User.apply_opN op [||]
    (Obj.magic
       [|
         wrap_mtbdd symbxLtThree;
         Obj.magic @@ Mtbdd.cst mgr tbl (Obj.magic (0, 0));
         Obj.magic @@ Mtbdd.cst mgr tbl (Obj.magic (1, 1));
       |])

let applyN ~f ~args _ =
  let args = Array.of_list args in
  let g _ (arr : 'a Cudd.Mtbdd.unique Cudd.Vdd.t array) : 'a Cudd.Mtbdd.unique Cudd.Vdd.t option =
    let cst = Array.fold_left (fun res add -> res && Mtbdd.is_cst add) true arr in
    if cst then
      let res =
        Array.fold_left
          (fun facc add -> Obj.magic (facc (Obj.magic (Mtbdd.dval add))))
          (Obj.magic f) arr
      in
      Some (Mtbdd.cst mgr tbl (Obj.magic res))
    else None
  in
  let op =
    User.make_opN ~memo:Cudd.(Cache (Cache.create (Array.length args))) 0 (Array.length args) g
  in
  User.apply_opN op [||] (Obj.magic args)

let v3 =
  applyN
    (fun b x y -> if b then x else y)
    [
      wrap_mtbdd symbxLtThree;
      Obj.magic @@ Mtbdd.cst mgr tbl (Obj.magic 0);
      Obj.magic @@ Mtbdd.cst mgr tbl (Obj.magic 1);
    ]
    0

let assertion_example =
  applyN (fun x y -> if x then true else if y then true else false) [xgttwo; ygttwo] 0

let prob = Mtbdd.cst mgr tbl_prob 0.5

let guard_true = Mtbdd.guard_of_leaf tbl assertion_example true

(* applyN((fun b v -> if ..), predicate, v) ) *)
let mapIf predicate (f : int -> int) (v : int Mtbdd.t) =
  let g b v = if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique tbl else v in
  let special bdd1 bdd2 =
    if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1)) then Some bdd2 else None
  in
  let op = User.make_op2 ~memo:Cudd.Memo.Global ~commutative:false ~idempotent:false ~special g in
  User.apply_op2 op predicate v

let v2 = mapIf (wrap_mtbdd symbxLtThree) (fun v -> v + 1) v

(* This returns 3 - which is right, 2 paths lead to 0 (MSB and 2-MSB being true) and one path leads to 1 (the inverse) *)
let sz = Mtbdd.nbpaths v2

(* One thing that this little experiment shows, is that we don't need to be very
explicit about what symbolics a value depends on; with the apply operation it
figured it out on its own, i.e. we never explicitly created a "map" (an MTBDD) from symbX to v. *)

(* if x<= 3 then
      if y = 3 then
         v+1 
      else v+2
    else v*)

let mapIte3 predicate1 predicate2 (v : int Mtbdd.t) (f : bool -> bool -> int -> int) =
  let g b1 b2 v = f (Mtbdd.get b1) (Mtbdd.get b2) (Mtbdd.get v) |> Mtbdd.unique tbl in
  let op = User.make_op3 ~memo:Cudd.Memo.Global g in
  User.apply_op3 op predicate1 predicate2 v

(* translation using nested applies *)
let exp =
  mapIte3 (wrap_mtbdd symbxLtThree) (wrap_mtbdd symbyEqThree) v (fun b1 b2 v ->
      if b1 then if b2 then v + 1 else v + 2 else v)
