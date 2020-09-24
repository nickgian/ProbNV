open Cudd

(* BDD Manager *)
let mgr = Man.make_v ();;

(* Leaf table *)
let tbl =
  Mtbdd.make_table
    ~hash:(Hashtbl.hash)
    ~equal:(=);;

(* A table to represent BDDs as MTBDDs - might not be necessary *)
let tbl_bool =
  Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

(* BDD to MTBDD *)
let wrap_mtbdd bdd =
  let tru = Mtbdd.cst mgr tbl_bool true in
  let fal = Mtbdd.cst mgr tbl_bool false in
  Mtbdd.ite bdd tru fal
    

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for _ = 1 to sz - num_vars do ignore (Bdd.newvar mgr) done;;

let ithvar i =
  set_size (i + 1) ;
  Bdd.ithvar mgr i;;

(* A "map", it does not depend on any symbolic right now, it's a leaf with value 0*)
let v = Mtbdd.cst mgr tbl 0;;

(* Creating a "symbolic", 4 bit-integer. *)
let symbx = Array.init 4 (fun j -> ithvar j);;
let symby = Array.init 4 (fun j -> ithvar (j+4));;

(* BDD function <= *)
let leq xs ys =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let acc = ref (Bdd.dtrue mgr) in
  Array.iter2 (fun x y -> 
    acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))) xs ys;
  !acc;;

let eq xs ys = 
  let acc = ref (Bdd.dtrue mgr) in
  Array.iter2 (fun x y -> 
    acc := Bdd.dand !acc (Bdd.eq x y)
  ) xs ys;
  !acc

let three = [|Bdd.dtrue mgr; Bdd.dtrue mgr; Bdd.dfalse mgr; Bdd.dfalse mgr|]

(* Set of 4-bit integers that are less or equal to three *)
let symbxLtThree = leq symbx three
let symbyEqThree = eq symby three

(* mapIf takes a predicate in the form a BDD (MTBDD with boolean leafs for library reasons, 
 * a function f from integers to integers
 * and v, a multi-terminal bdd with int leafs
 * and combines the predicate and the MTBDD by applying f over the leafs of v when the predicate is true. *)

(* An optimization (that will be good to do when possible) is implemented using the special argument.
 * If special bdd1 bdd2 = Some res then a full recursive descent is not required.
 * For mapIf, basically for paths of the predicate's tree which are constant and false, we don't need to visit the leafs of the MTBDD v, the result is v.
*)

(* applyN((fun b v -> if ..), predicate, v) ) *)
let mapIf predicate (f : int -> int) (v : int Mtbdd.t) = 
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique tbl else v
  in
  let special = fun bdd1 bdd2 ->
      if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
      then Some bdd2
      else None
  in
  let op =
    User.make_op2
      ~memo:(Cudd.Memo.Global)
      ~commutative:false ~idempotent:false ~special:special g
  in
  User.apply_op2 op predicate v;;

let v2 = mapIf (wrap_mtbdd symbxLtThree) (fun v -> v + 1) v;;

(* This returns 3 - which is right, 2 paths lead to 0 (MSB and 2-MSB being true) and one path leads to 1 (the inverse) *)
let sz = Mtbdd.nbpaths v2;;

(* One thing that this little experiment shows, is that we don't need to be very
explicit about what symbolics a value depends on; with the apply operation it
figured it out on its own, i.e. we never explicitly created a "map" (an MTBDD) from symbX to v. *)

(* if x<= 3 then
      if y = 3 then
         v+1 
      else v+2
    else v*)

let mapIte3 predicate1 predicate2 (v : int Mtbdd.t) (f: bool -> bool -> int -> int)  = 
  let g b1 b2 v =
    f (Mtbdd.get b1) (Mtbdd.get b2) (Mtbdd.get v) |> Mtbdd.unique tbl
  in
  let op =
    User.make_op3
      ~memo:(Cudd.Memo.Global) g
  in
  User.apply_op3 op predicate1 predicate2 v;;

(* translation using nested applies *)
let exp = mapIte3 (wrap_mtbdd symbxLtThree) (wrap_mtbdd symbyEqThree) v
                  (fun b1 b2 v ->
                    if b1 then 
                      if b2 then
                        v+1
                      else v+2
                    else v)             