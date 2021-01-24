open ProbNv_lang
(** * Compiles a program in the LLL to an OCaml program*)

open ProbNv_utils
open PrimitiveCollections
open Collections
open Syntax
open ProbNv_datastructures
open CompileBDDs
open Batteries

let varname x = Var.to_string_delim "_" x

(** Translating probNV records to OCaml records (type or values depending on f)*)
let record_to_ocaml_record (sep : string) (f : 'a -> string)
    (map : 'a StringMap.t) : string =
  let entries =
    StringMap.fold
      (fun l e acc -> Printf.sprintf "%s%s %s %s;" acc l sep (f e))
      map ""
  in
  Printf.sprintf "{ %s }" entries

(** Keeps track of the tuple-sizes used throughout the program *)
let record_table = ref IntSet.empty

let proj_rec i n =
  record_table := IntSet.add n !record_table;
  Printf.sprintf "p%d__%d" i n

(* don't call with a negative n... *)
let rec fold_int (f : int -> 'a -> 'a) acc n =
  if n = 0 then acc else fold_int f (f n acc) (n - 1)

(** For each tuple of size n creates a corresponding record*)
let build_record_type n =
  let lst = BatList.init n (fun i -> i) in
  let type_vars =
    Collections.printList (fun i -> Printf.sprintf "'a%d" i) lst "(" ", " ")"
  in
  let proj_vars =
    Collections.printList
      (fun i -> Printf.sprintf "p%d__%d : 'a%d" i n i)
      lst "{" "; " "}"
  in
  Printf.sprintf "%s tup__%d = %s" type_vars n proj_vars

let build_record_types () =
  let lst = IntSet.to_list !record_table in
  match lst with
  | [] -> ""
  | _ ->
      Collections.printList
        (fun n -> build_record_type n)
        lst "type " "\n and " "\n"

let build_proj_func n =
  let lst = BatList.init n (fun i -> i) in
  Collections.printList
    (* (fun i -> Printf.sprintf "| \"p%d__%d\" -> Obj.magic (fun x -> x.p%d__%d)" i n i n) *)
      (fun i ->
      Printf.sprintf "| (%d,%d) -> Obj.magic (fun x -> x.p%d__%d)" i n i n)
    lst "" "\n" "\n"

(** Builds a table (function) that maps record projector names to the respective
   functions *)
let build_proj_funcs () =
  let branches =
    IntSet.fold
      (fun n acc -> Printf.sprintf "%s%s" (build_proj_func n) acc)
      !record_table ""
  in
  if String.equal "" branches then
    "let record_fns s = failwith \"Should not execute\""
  else Printf.sprintf "let record_fns s = match s with \n%s" branches

let build_constructor n =
  let lst = BatList.init n (fun i -> i) in
  let fun_args =
    Collections.printList
      (fun i -> Printf.sprintf "p%d__%d" i n)
      lst "fun " " " " -> "
  in
  let fun_body =
    Collections.printList
      (fun i -> Printf.sprintf "p%d__%d" i n)
      lst "{" "; " "}"
  in
  Printf.sprintf "| %d -> Obj.magic (%s%s)\n" n fun_args fun_body

(** Builds a table (function) that maps each record to a function that takes as
   arguments a value for each of its fields and creates the record*)
let build_constructors () =
  let branches =
    IntSet.fold
      (fun n acc -> Printf.sprintf "%s%s" (build_constructor n) acc)
      !record_table ""
  in
  if String.equal "" branches then
    "let record_cnstrs s = failwith \"Should not execute\""
  else Printf.sprintf "let record_cnstrs s = match s with \n%s" branches

let is_prefix_op op =
  match op with
  | BddAnd | BddOr | BddAdd _ | BddNot | BddLess _ | BddLeq _ | BddEq | MGet
  | MCreate | MSet | TGet _ ->
      true
  | And | Or | Not | UAdd _ | Eq | ULess _ | ULeq _ | NLess | NLeq ->
      false

(** Translating LLL operators to OCaml operators*)
let op_to_ocaml_string op =
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "not"
  | UAdd _ -> "+"
  (* | USub _ -> "-" *)
  (* | UAnd _ -> "land" *)
  | Eq -> "="
  | ULess _ -> "<"
  | ULeq _ -> "<="
  | NLess -> "<"
  | NLeq -> "<="
  | BddAnd | BddOr | BddNot | BddEq | BddAdd _ | BddLess _ | BddLeq _ | MGet
  | MSet | MCreate | TGet _ ->
      failwith ("Operation: " ^ (Printing.op_to_string op) ^ ", prefix operations are handled elsewhere")

(** Translating patterns to OCaml patterns*)

let rec pattern_to_ocaml_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> varname x
  | PBool true -> "true"
  | PBool false -> "false"
  | PInt i -> string_of_int (Integer.to_int i)
  | PTuple ps ->
      let n = BatList.length ps in
      Collections.printListi
        (fun i p ->
          Printf.sprintf "%s = %s" (proj_rec i n) (pattern_to_ocaml_string p))
        ps "{" "; " "}"
  | POption None -> "None"
  | POption (Some p) -> Printf.sprintf "Some %s" (pattern_to_ocaml_string p)
  | PRecord _ -> failwith "Records should have been unrolled"
  | PNode n -> Printf.sprintf "%d" n
  | PEdge (p1, p2) ->
      Printf.sprintf "(%s, %s)"
        (pattern_to_ocaml_string p1)
        (pattern_to_ocaml_string p2)

(** ProbNv types to OCaml types*)
let rec ty_to_ocaml_string t =
  match t.typ with
  | TVar { contents = Link ty } -> ty_to_ocaml_string ty
  | TVar { contents = Unbound _ } -> failwith "unbound var"
  | QVar name -> Printf.sprintf "'%s" (varname name)
  | TBool -> "bool"
  | TInt _ -> "int"
  | TNode -> "int"
  | TEdge -> "(int * int)"
  | TArrow (t1, t2) ->
      Printf.sprintf "%s -> %s" (ty_to_ocaml_string t1) (ty_to_ocaml_string t2)
  | TTuple ts ->
      let n = BatList.length ts in
      record_table := IntSet.add n !record_table;
      (*add type to record table*)
      let tup_typ = Printf.sprintf ") tup__%d" n in
      Collections.printList
        (fun ty -> Printf.sprintf "%s" (ty_to_ocaml_string ty))
        ts "(" "," tup_typ
  | TOption t -> Printf.sprintf "(%s) option" (ty_to_ocaml_string t)
  | TMap (kty, vty) ->
      ignore (ty_to_ocaml_string kty);
      (* NOTE: doing this for the side effect in the case of TTuple, i.e. adding to record_table *)
      ignore (ty_to_ocaml_string vty);
      let vty = ty_to_ocaml_string vty in
      Printf.sprintf "(%s) CompileBDDs.t" vty
  | TRecord _ -> failwith "Records should have been unrolled"

(* 
   | TRecord map -> record_to_ocaml_record ":" ty_to_ocaml_string map *)

let rec pattern_vars p =
  match p with
  | PWild | PBool _ | PInt _ | POption None | PNode _ ->
      BatSet.PSet.create Var.compare
  | PVar v -> BatSet.PSet.singleton ~cmp:Var.compare v
  | PEdge (p1, p2) -> pattern_vars (PTuple [ p1; p2 ])
  | PTuple ps ->
      List.fold_left
        (fun set p -> BatSet.PSet.union set (pattern_vars p))
        (BatSet.PSet.create Var.compare)
        ps
  | POption (Some p) -> pattern_vars p
  | PRecord _ -> failwith "Records should have been unrolled"

(* | PRecord map ->
    StringMap.fold
      (fun _ p set -> BatSet.PSet.union set (pattern_vars p))
      map
      (PSet.create Var.compare) *)

let rec free (seen : Var.t BatSet.PSet.t) (e : exp) : Var.t BatSet.PSet.t =
  match e.e with
  | EVar v ->
      if BatSet.PSet.mem v seen then BatSet.PSet.create Var.compare
      else BatSet.PSet.singleton ~cmp:Var.compare v
  | EVal _ -> BatSet.PSet.create Var.compare
  | EOp (_, es) | ETuple es ->
      List.fold_left
        (fun set e -> BatSet.PSet.union set (free seen e))
        (BatSet.PSet.create Var.compare)
        es
  | EFun f -> free (BatSet.PSet.add f.arg seen) f.body
  | EApp (e1, e2) -> BatSet.PSet.union (free seen e1) (free seen e2)
  | EIf (e1, e2, e3) ->
      BatSet.PSet.union (free seen e1)
        (BatSet.PSet.union (free seen e2) (free seen e3))
  | ELet (x, e1, e2) ->
      let seen = BatSet.PSet.add x seen in
      BatSet.PSet.union (free seen e1) (free seen e2)
  | ESome e -> free seen e
  | EMatch (e, bs) ->
      let bs1 =
        PatMap.fold
          (fun p e set ->
            let seen = BatSet.PSet.union seen (pattern_vars p) in
            BatSet.PSet.union set (free seen e))
          bs.pmap
          (BatSet.PSet.create Var.compare)
      in
      let bs =
        BatList.fold_left
          (fun set (p, e) ->
            let seen = BatSet.PSet.union seen (pattern_vars p) in
            BatSet.PSet.union set (free seen e))
          bs1 bs.plist
      in
      BatSet.PSet.union (free seen e) bs
  | ERecord _ | EProject _ -> failwith "records should have been unrolled"
  | EBddIf _ | EToBdd _ | EToMap _ | EApplyN _ ->
      failwith "Does not apply to non-concrete expressions"

(** Returns an OCaml string that contains the hashconsed int of the function
   body and a tuple with the free variables that appear in the function. Used
   for caching BDD operations.
    NOTE: In general this is sound only if you inline, because we do not capture the environment
    of any function that is called and may have free variables.
*)

let getFuncCache (e : exp) : string =
  match e.e with
  | EFun f ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
      let free = free seen f.body in
      let freeList = BatSet.PSet.to_list free in
      let closure =
        Collections.printList (fun x -> varname x) freeList "(" "," ")"
      in
      Printf.sprintf "(%d, %s)"
        (Collections.ExpIds.fresh_id exp_store f.body)
        closure
  | _ ->
      (*assume there are no free variables, but this needs to be fixed: always inline*)
      Printf.sprintf "(%d, ())" (Collections.ExpIds.fresh_id exp_store e)

(** Function walking through an expression to record tuple types.
    This is done by the compiler on the go, but not for
    operations like mapIte because these expressions are never translated to OCaml, so we manually have to do it.
   Expect this function to be called somewhere in the MapIte case.*)

(* 
let rec track_tuples_exp e =
  match e.e with
  | ETuple es ->
      let n = BatList.length es in
      List.iteri (fun i _ -> ignore (proj_rec i n)) es
  | EMatch (_, bs) -> List.iter (fun (p, _) -> track_tuples_pattern p) (branchToList bs)
  | EVal v -> (
      match v.v with
      | VTuple vs ->
          let n = BatList.length vs in
          List.iteri (fun i _ -> ignore (proj_rec i n)) vs
      | _ -> () )
  | EOp (TGet (sz, lo, _), _) -> ignore (proj_rec lo sz)
  | EOp (TSet (sz, lo, _), _) -> ignore (proj_rec lo sz)
  | EVar _ | EFun _ | EApp _ | ELet _ | ESome _ | ETy _ | ERecord _ | EProject _ | EIf _ | EOp _ ->
      ()

and track_tuples_pattern p =
  match p with
  | PTuple ps ->
      let n = BatList.length ps in
      List.iteri
        (fun i p ->
          ignore (proj_rec i n);
          track_tuples_pattern p)
        ps
  | POption (Some p) -> track_tuples_pattern p
  (* records are already unrolled  *)
  | POption None | PWild | PVar _ | PUnit | PBool _ | PInt _ | PRecord _ | PNode _ | PEdge _ -> () *)

let magic s = Printf.sprintf "(Obj.magic %s)" s

(** Translating values and expressions to OCaml*)
let rec value_to_ocaml_string v =
  match v.v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> string_of_int (Integer.to_int i)
  | VTuple vs ->
      let n = BatList.length vs in
      Collections.printListi
        (fun i v ->
          Printf.sprintf "%s = %s" (proj_rec i n) (value_to_ocaml_string v))
        vs "{" "; " "}"
  | VOption None -> "None"
  | VOption (Some v) -> Printf.sprintf "(Some %s)" (value_to_ocaml_string v)
  | VRecord _ -> failwith "Records should have been unrolled"
  | VNode n -> string_of_int n
  | VEdge (n1, n2) -> Printf.sprintf "(%d, %d)" n1 n2
  | VClosure _ -> failwith "Closures shouldn't appear here."
  | VTotalMap _ ->
      failwith
        "Total maps do not have a syntactic value and should not appear here."

and exp_to_ocaml_string e =
  match e.e with
  | EVar x -> varname x
  | EVal v -> value_to_ocaml_string v
  | EOp (op, es) when is_prefix_op op ->
      prefix_op_to_ocaml_string op es (OCamlUtils.oget e.ety)
  | EOp (op, es) -> op_args_to_ocaml_string op es
  | EFun f -> func_to_ocaml_string f
  | EApp (e1, e2) ->
      Printf.sprintf "((%s) (%s))" (exp_to_ocaml_string e1)
        (exp_to_ocaml_string e2)
  | EIf (e1, e2, e3) ->
      Printf.sprintf "(if %s then\n %s else\n %s)" (exp_to_ocaml_string e1)
        (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
  | ELet (x, e1, e2) ->
      Printf.sprintf "(let %s = %s in\n %s)" (varname x)
        (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
  | EBddIf (e1, e2, e3) ->
      Printf.sprintf "(BddFunc.ite %s %s %s)" (exp_to_ocaml_string e1)
        (exp_to_ocaml_string e2) (exp_to_ocaml_string e3)
  | EToBdd e1 ->
      Printf.sprintf "(BddFunc.toBdd record_fns ~vty_id:%d %s)"
        (get_fresh_type_id type_store (OCamlUtils.oget e1.ety))
        (exp_to_ocaml_string e1)
  | EToMap e1 ->
      Printf.sprintf "(BddFunc.toMap ~value:%s)" (exp_to_ocaml_string e1)
  | EApplyN (e1, es) -> (
      let el1 = exp_to_ocaml_string e1 in
      let esl =
        List.map
          (fun e ->
            if get_mode (OCamlUtils.oget e.ety) = Some Symbolic then
              magic
              @@ Printf.sprintf "(BddFunc.wrap_mtbdd (%s))"
                   (exp_to_ocaml_string e)
            else magic @@ exp_to_ocaml_string e)
          es
      in
      ignore (get_fresh_type_id type_store (OCamlUtils.oget e.ety));

      (*cache user op on e1 *)
      (* Get e1's hashcons and closure *)
      let op_key = getFuncCache e1 in
      (*FIXME: this needs to be fresh, to avoid the case where it is
                used inside e1 but our separator is not OCaml friendly*)
      let op_key_var = "op_key" in
      (* special cases *)
      match esl with
      | [ v1 ] ->
          Printf.sprintf
            "(Obj.magic (let %s = %s in \n\
            \ BddFunc.apply1 ~op_key:(Obj.magic %s) ~f:%s ~arg1:%s))" op_key_var
            op_key op_key_var el1 v1
      | [ v1; v2 ] ->
          Printf.sprintf
            "(Obj.magic (let %s = %s in \n\
            \ BddFunc.apply2 ~op_key:(Obj.magic %s) ~f:%s ~arg1:%s ~arg2:%s))"
            op_key_var op_key op_key_var el1 v1 v2
      | [ v1; v2; v3 ] ->
          Printf.sprintf
            "(Obj.magic (let %s = %s in \n\
            \ BddFunc.apply3 ~op_key:(Obj.magic %s) ~f:%s ~arg1:%s ~arg2:%s \
             ~arg3:%s))"
            op_key_var op_key op_key_var el1 v1 v2 v3
      | _ ->
          let esl_array =
            Collections.printList (fun el -> el) esl "[|" "; " "|]"
          in
          Printf.sprintf "(BddFunc.applyN ~f:%s ~args:(%s))" el1 esl_array )
  | ETuple es ->
      let n = BatList.length es in
      Collections.printListi
        (fun i e ->
          Printf.sprintf "%s = %s" (proj_rec i n) (exp_to_ocaml_string e))
        es "{" "; " "}"
  | EMatch (e1, bs) ->
      Printf.sprintf "(match %s with \n %s)" (exp_to_ocaml_string e1)
        (Collections.printList branch_to_ocaml_string (branchToList bs) "" ""
           "")
  | ESome e -> Printf.sprintf "Some (%s)" (exp_to_ocaml_string e)
  | ERecord _ | EProject _ -> failwith "Records should have been unrolled"

and op_args_to_ocaml_string op es =
  match es with
  | [] -> failwith "Empty operand list"
  | [ e1 ] ->
      Printf.sprintf "(%s %s)" (op_to_ocaml_string op) (exp_to_ocaml_string e1)
  | [ e1; e2 ] ->
      Printf.sprintf "(%s %s %s)" (exp_to_ocaml_string e1)
        (op_to_ocaml_string op) (exp_to_ocaml_string e2)
  | _ -> failwith "Should be a keyword op"

and prefix_op_to_ocaml_string op es ty =
  match es with
  | [] -> failwith "Operation with empty arguments"
  | [ e ] -> (
      match op with
      | BddNot -> Printf.sprintf "(BddFunc.bnot %s)" (exp_to_ocaml_string e)
      | MCreate -> (
          match ty.typ with
          | TMap (kty, vty) ->
              Printf.sprintf
                "(Obj.magic (BddMap.create ~key_ty_id:(%d) ~val_ty_id:(%d) \
                 (Obj.magic (%s))))"
                (get_fresh_type_id type_store kty)
                (get_fresh_type_id type_store vty)
                (exp_to_ocaml_string (BatList.hd es))
          | _ -> failwith "Wrong type for map operation" )
      | TGet (idx, sz) ->
          let proj = proj_rec idx sz in
          Printf.sprintf "(%s).%s" (exp_to_ocaml_string e) proj
      | _ -> failwith "Wrong number of arguments" )
  | [ e1; e2 ] -> (
      match op with
      | BddAnd ->
          Printf.sprintf "(BddFunc.band %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | BddOr ->
          Printf.sprintf "(BddFunc.bor %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | BddAdd _ ->
          Printf.sprintf "(BddFunc.add %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | BddLess _ ->
          Printf.sprintf "(BddFunc.lt %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | BddLeq _ ->
          Printf.sprintf "(BddFunc.leq %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | BddEq ->
          Printf.sprintf "(BddFunc.eq %s %s)" (exp_to_ocaml_string e1)
            (exp_to_ocaml_string e2)
      | MGet ->
          Printf.sprintf
            "(Obj.magic (BddMap.find record_fns (%s) (Obj.magic (%s))))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
      | MSet | MCreate ->
          failwith "Wrong number of arguments to MSet/MCreate operation"
      | Eq | UAdd _ | ULess _ | NLess | ULeq _ | NLeq | And | Or | Not | BddNot
      | TGet _ ->
          failwith "not applicable" )
  | [ e1; e2; e3 ] -> (
      match op with
      | MSet ->
          Printf.sprintf
            "(Obj.magic (BddMap.update record_fns (%s) (Obj.magic (%s)) \
             (Obj.magic (%s))))"
            (exp_to_ocaml_string e1) (exp_to_ocaml_string e2)
            (exp_to_ocaml_string e3)
      | And | Or | Not | Eq | NLess | NLeq | MGet | MCreate | BddAnd | BddOr
      | BddNot | BddEq | UAdd _ | ULess _ | ULeq _ | BddAdd _ | BddLess _
      | BddLeq _ | TGet _ ->
          failwith "Wrong number of arguments to operation." )
  | _ -> failwith "too many arguments to operation"

and func_to_ocaml_string f =
  Printf.sprintf "(fun %s -> %s)" (varname f.arg) (exp_to_ocaml_string f.body)

and branch_to_ocaml_string (p, e) =
  Printf.sprintf "| %s -> %s\n"
    (pattern_to_ocaml_string p)
    (exp_to_ocaml_string e)

(** Translate a declaration to an OCaml program*)
let compile_decl decl =
  match decl with
  | DUserTy _ -> ""
  | DSymbolic (x, ty, _) ->
      let ty_id = get_fresh_type_id type_store ty in
      Printf.sprintf "let %s = BddFunc.create_value %d SIM.graph\n" (varname x)
        ty_id
  | DLet (x, e) ->
      Printf.sprintf "let %s = %s" (varname x) (exp_to_ocaml_string e)
  | DAssert (e, prob) ->
      Printf.sprintf "let () = SIM.assertions := (%s, %f) :: !SIM.assertions\n"
        (exp_to_ocaml_string e) prob
  | DSolve solve -> (
      match solve.var_names.e with
      | EVar x -> (
          match solve.aty with
          | None -> failwith "cannot solve without an attribute type"
          | Some attr ->
              (*NOTE: this is just the attribute type, not including the map from nodes to attributes *)
              (*need to register node types manually! *)
              ignore (get_fresh_type_id type_store (concrete TNode));
              Printf.printf "Solution type: %s\n" (Printing.ty_to_string attr);
              let attr_id = get_fresh_type_id type_store attr in

              (* ignore (exp_to_ocaml_string solve.init);
                 ignore (exp_to_ocaml_string solve.trans);
                 ignore (exp_to_ocaml_string solve.merge);
                 Printf.sprintf
                   "let s_120 = SIM.simulate_solve record_fns (2) (\"s\") ((fun \
                    u_121 -> (BddFunc.toMap ~value:((init_118) (u_121))))) ((fun \
                    e_122 -> (fun x_123 -> (Obj.magic (let op_key = (1, \
                    (trans_108,e_122)) in\n\
                   \                 BddFunc.apply1 ~op_key:(Obj.magic op_key) \
                    ~f:(fun x_123 -> ((((trans_108) (e_122))) (x_123))) \
                    ~arg1:(Obj.magic x_123)))))) ((fun u_113 -> (fun r1_114 -> \
                    (fun r2_115 -> (Obj.magic (let op_key = (0, ()) in\n\
                   \              let arg2 = BddFunc.apply2 ~op_key:(Obj.magic \
                    (3, ())) ~f:(fun b -> fun x -> if b then None else x) \
                    ~arg1:(Obj.magic (BddFunc.wrap_mtbdd (((isFailed_106) \
                    (u_113))))) ~arg2:(Obj.magic r2_115) in\n\
                   \              let arg3 = BddFunc.apply2 ~op_key:(Obj.magic \
                    (4, ())) ~f:(fun b -> fun x -> if b then None else x) \
                    ~arg1:(Obj.magic (BddFunc.wrap_mtbdd (((isFailed_106) \
                    (u_113))))) ~arg2:(Obj.magic r1_114) in\n\n\
                   \                               BddFunc.apply2 \
                    ~op_key:(Obj.magic op_key) ~f:(fun r2_42 -> (fun r1_41 ->\n\
                   \              (match {p0__2 = r1_41; p1__2 = r2_42} with \n\
                   \              | {p0__2 = _; p1__2 = None} -> r1_41\n\
                   \             | {p0__2 = None; p1__2 = _} -> r2_42\n\
                   \             | {p0__2 = Some a_59; p1__2 = Some b_60} -> (if \
                    (a_59 <= b_60) then\n\
                   \              Some (a_59) else\n\
                   \              Some (b_60))\n\
                   \             ))) ~arg1:(Obj.magic arg2) ~arg2:(Obj.magic \
                    arg3)))))))" *)
              (* Printf.sprintf
                 "let s_47 = SIM.simulate_solve record_fns (2) (\"s\") ((fun \
                  u_48 -> (BddFunc.toMap ~value:((init_45) (u_48))))) ((fun \
                  e_49 -> (fun x_50 -> (Obj.magic (let op_key = (1, \
                  (trans_35,e_49)) in\n\
                 \              BddFunc.apply1 ~op_key:(Obj.magic op_key) \
                  ~f:(fun x_50 -> ((((trans_35) (e_49))) (x_50))) \
                  ~arg1:(Obj.magic x_50)))))) \n\
                 \              \n\
                 \              ((fun u_40 -> (fun r1_41 -> (fun r2_42 -> \
                  (Obj.magic (let op_key = (0, ()) in\n\
                 \              let arg2 = BddFunc.apply2 ~op_key:(Obj.magic \
                  (3, ())) ~f:(fun b -> fun x -> if b then None else x) \
                  ~arg1:(Obj.magic (BddFunc.wrap_mtbdd (((isFailed_33) \
                  (u_40))))) ~arg2:(Obj.magic r2_42) in\n\
                 \              let arg3 = BddFunc.apply2 ~op_key:(Obj.magic \
                  (4, ())) ~f:(fun b -> fun x -> if b then None else x) \
                  ~arg1:(Obj.magic (BddFunc.wrap_mtbdd (((isFailed_33) \
                  (u_40))))) ~arg2:(Obj.magic r1_41) in\n\
                 \            \n\
                 \              BddFunc.apply2 ~op_key:(Obj.magic op_key) \
                  ~f:(fun r2_42 -> (fun r1_41 ->\n\
                 \              (match {p0__2 = r1_41; p1__2 = r2_42} with \n\
                 \              | {p0__2 = _; p1__2 = None} -> r1_41\n\
                 \             | {p0__2 = None; p1__2 = _} -> r2_42\n\
                 \             | {p0__2 = Some a_59; p1__2 = Some b_60} -> (if \
                  (a_59 <= b_60) then\n\
                 \              Some (a_59) else\n\
                 \              Some (b_60))\n\
                 \             ))) ~arg1:(Obj.magic arg2) ~arg2:(Obj.magic \
                  arg3)))))))" *)
              (* Printf.sprintf
                 "let s_63 = SIM.simulate_solve record_fns (2) (\"s\")\n\
                 \                     ((fun u_64 -> (BddFunc.toMap \
                  ~value:((init_61) (u_64)))))\n\
                 \                     ((fun e_65 -> (fun x_66 -> (Obj.magic \
                  (let op_key = (1, (trans_51,e_65)) in\n\
                 \                  BddFunc.apply1 ~op_key:(Obj.magic op_key) \
                  ~f:(fun x_66 -> ((((trans_51) (e_65))) (x_66))) \
                  ~arg1:(Obj.magic x_66))))))\n\n\
                 \                  ((fun u_56 -> (fun r1_57 -> (fun r2_58 -> \
                  (Obj.magic (let op_key = (0, ()) in\n\
                 \                  let arg2 = BddFunc.apply2 \
                  ~op_key:(Obj.magic (3, ())) ~f:(fun b -> fun x -> if b then \
                  None else x) ~arg1:(Obj.magic (BddFunc.wrap_mtbdd \
                  (((isFailed_49) (u_56))))) ~arg2:(Obj.magic r2_58) in\n\
                 \                  let arg3 = BddFunc.apply2 \
                  ~op_key:(Obj.magic (4, ())) ~f:(fun b -> fun x -> if b then \
                  None else x) ~arg1:(Obj.magic (BddFunc.wrap_mtbdd \
                  (((isFailed_49) (u_56))))) ~arg2:(Obj.magic r1_57) in\n\
                 \                  BddFunc.apply2 ~op_key:(Obj.magic op_key) \
                  ~f:(fun r2_58 -> (fun r1_57 ->\n\
                 \                  (match {p0__2 = r1_57; p1__2 = r2_58} with\n\
                 \                  | {p0__2 = _; p1__2 = None} -> r1_57\n\
                 \                 | {p0__2 = None; p1__2 = _} -> r2_58\n\
                 \                 | {p0__2 = Some a_59; p1__2 = Some b_60} -> \
                  (if (a_59 <= b_60) then\n\
                 \                  Some (a_59) else\n\
                 \                  Some (b_60))\n\
                 \                 ))) ~arg1:(Obj.magic arg2) ~arg2:(Obj.magic \
                  arg3)))))))" *)
              Printf.sprintf
                "let %s = SIM.simulate_solve record_fns (%d) (\"%s\") (%s) \
                 (%s) (%s)"
                (varname x) attr_id (Var.name x)
                (exp_to_ocaml_string solve.init)
                (exp_to_ocaml_string solve.trans)
                (exp_to_ocaml_string solve.merge) )
      | _ ->
          failwith "Not implemented" (* Only happens if we did map unrolling *)
      )
  | DNodes _ | DEdges _ ->
      (*nodes and edges are not emmited in the OCaml program *)
      ""

let compile_decls decls =
  let s = Collections.printList compile_decl decls "" "\n\n" "\n" in
  let tuple_s = build_record_types () in
  let record_fns = build_proj_funcs () in
  let record_cnstrs = build_constructors () in
  let embeddings = "let _ = Embeddings.build_embed_cache record_fns\n\n" in

  Printf.sprintf "%s %s %s %s %s" tuple_s record_cnstrs record_fns embeddings s

(* let _ = Embeddings.build_unembed_cache record_cnstrs record_fns *)

let set_entry (name : string) =
  Printf.sprintf
    "let () = SrpNative.srp := Some (module %s:SrpNative.CompleteSRPSig)" name

let generate_ocaml (name : string) decls =
  let header =
    Printf.sprintf
      "open ProbNv_datastructures\n\
      \ open ProbNv_lang\n\
       open Syntax\n\
       open ProbNv_compile\n\n\
       module %s (SIM:SrpNative.SrpSimulationSig): SrpNative.NATIVE_SRP = struct\n"
      name
  in
  let ocaml_decls =
    Profile.time_profile "Compilation Time" (fun () -> compile_decls decls)
  in
  Printf.sprintf "%s %s end\n %s" header ocaml_decls (set_entry name)

(* Create the plugin that we will dynamically load later, do not print warnings
   do not treat them as errors*)
let build_dune_file name =
  Printf.sprintf
    "(library \n\
    \ (name %s_plugin) \n\
    \ (public_name %s.plugin)\n\
    \ (modes native)\n\
    \ (libraries probNv))\n\
    \ (env\n\
    \ (dev\n\
    \ (flags (:standard -warn-error -A -w -a -opaque))))" name name

let build_project_file name = Printf.sprintf "(lang dune 1.10)\n (name %s)" name

let build_opam_file name =
  Printf.sprintf
    "name: \"%s-plugin\"\n\
    \ build: [ \"dune\" \"build\" \"-p\" name \"-j\" jobs ]" name

let print_file file s =
  let oc =
    open_out_gen [ Open_rdonly; Open_wronly; Open_creat; Open_trunc ] 0o777 file
  in
  Printf.fprintf oc "%s" s;
  close_out oc

(* TODO: should use srcdir env. Or even better get rid of source all together,
   find out how to generate and link cmxs files from build directory*)
let compile_command_ocaml name =
  let dune = build_dune_file name in
  let project = build_project_file name in
  let opam = build_opam_file name in
  print_file "dune" dune;
  print_file "dune-project" project;
  print_file (name ^ ".opam") opam;
  Sys.command "dune build; dune install"

(* Sys.command "dune build command >>/dev/null 2>&1; sudo dune install command >>/dev/null 2>&1" *)

let compile_ocaml name net =
  let basename = Filename.basename name in
  let program = generate_ocaml basename net in
  let src_dir =
    try Sys.getenv "PROBNV_BUILD" ^ name
    with Not_found ->
      failwith
        "To use compiler, please set environment variable PROBNV_BUILD to a \
         directory in which to generate build files. Use something outside the \
         nv directory."
  in
  (try Unix.mkdir src_dir 0o777 with _ -> ());
  let curdir = Sys.getcwd () in
  Unix.chdir src_dir;
  print_file (name ^ ".ml") program;
  let ret = compile_command_ocaml name in
  Unix.chdir curdir;
  ret
