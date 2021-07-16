(* Printing utilities for abstract syntax *)
open Batteries
open Syntax
open ProbNv_datastructures
open ProbNv_utils.PrimitiveCollections
open Cudd
open ProbNv_utils
open ProbNv_utils.RecordUtils

(* For printing maps, temporary *)
let rec ty_to_size ty =
  match (get_inner_type ty).typ with
  | TBool -> 1
  | TInt n -> n
  | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TOption tyo -> 1 + ty_to_size tyo
  | TNode -> ty_to_size (concrete (TInt !tnode_sz)) (* Encode as int *)
  | TEdge -> ty_to_size (concrete (TInt !tedge_sz)) (*Encode as edge id *)
  | TArrow _ | TVar _ | QVar _ | TMap _ | TRecord _ | TFloat ->
      failwith "internal error (ty_to_size):"

let tbool_to_bool tb =
  match tb with Man.False | Man.Top -> false | Man.True -> true

let vars_to_value_old vars ty =
  let open RecordUtils in
  let rec aux idx ty =
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
    | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
              let v, i = aux idx ty in
              (v :: vs, i))
            ([], idx) ts
        in
        (vtuple (List.rev vs), i)
    | TNode -> (
        (* Was encoded as int, so decode same way *)
        match aux idx (concrete (TInt !tnode_sz)) with
        | { v = VInt n; _ }, i -> (vnode (Integer.to_int n), i)
        | _ -> failwith "impossible" )
    | TEdge -> (
        match aux idx (concrete (TInt !tedge_sz)) with
        | { v = VInt n; _ }, i ->
            let u, v =
              PrimitiveCollections.IntMap.find (Integer.to_int n) !edge_mapping
            in

            (vedgeRaw (u, v), i)
        | _ -> failwith "impossible" )
    | TOption tyo ->
        let tag = tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v = if tag then voption (Some v) else voption None in
        (v, i)
    | TArrow _ | TMap _ | TVar _ | QVar _ | TRecord _ | TFloat ->
        failwith "internal error (bdd_to_value)"
  in
  fst (aux 0 ty)

let count_tops cube i sz =
  let count = ref 0 in
  for k = i to sz do
    if cube.(k) = Man.Top then incr count
  done;
  !count

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

let bindingsOld (map, ty) : (value * value) list =
  let bs = ref [] in
  let seen = Hashtbl.create 50 in
  Mtbddc.iter_cube
    (fun vars v ->
      let lst = Array.to_list vars in
      let sz = ty_to_size ty in
      let expanded =
        if count_tops vars 0 sz <= 1 then expand lst sz else [ lst ]
      in
      List.iter
        (fun vars ->
          let k = vars_to_value_old (Array.of_list vars) ty in
          if Hashtbl.mem seen k then ()
          else (
            Hashtbl.add seen k true;
            bs := (k, v) :: !bs ))
        expanded)
    map;
  !bs

let is_keyword_op op = match op with MMerge -> true | _ -> false

(* set to true if you want to print universal quanifiers explicitly *)
let quantifiers = true

let max_prec = 10

let prec_op op =
  match op with
  | And | BddAnd -> 7
  | Or | BddOr -> 7
  | Not | BddNot -> 6
  | FDiv | FMul -> 4
  | UAdd _ | UAnd _ | BddUAnd _ | BddAdd _ | FAdd -> 4
  (* | USub _ -> 4 *)
  | Eq | BddEq -> 5
  | MCreate -> 5
  | MGet -> 5
  | MSet -> 3
  | ULess _ | BddLess _ | NLess | ULeq _ | NLeq | BddLeq _ | ELess | ELeq -> 5
  | TGet _ -> 5
  | MMerge | MSize -> 3
  | FLess | FLeq -> 5

let prec_exp e =
  match e.e with
  | EVar _ -> 0
  | EVal _ -> 0
  | EOp (op, _) -> prec_op op
  | EFun _ -> 8
  | EApp _ -> max_prec
  | EIf _ -> max_prec
  | ELet _ -> max_prec
  | EApplyN _ -> max_prec
  | EToBdd _ -> max_prec
  | EToMap _ -> max_prec
  | EBddIf _ -> max_prec
  | EMatch _ -> 8
  | ETuple _ -> 0
  | ESome _ -> max_prec
  | ERecord _ -> 0
  | EProject _ -> 0

let rec sep s f xs =
  match xs with
  | [] -> ""
  | [ x ] -> f x
  | x :: y :: rest -> f x ^ s ^ sep s f (y :: rest)

let rec term s f xs =
  match xs with [] -> "" | _ -> PrimitiveCollections.printList f xs "" s ""

let comma_sep f xs = sep "," f xs

let semi_sep f xs = sep ";" f xs

let semi_term f xs = term ";" f xs

let list_to_string f lst = PrimitiveCollections.printList f lst "[" ";" "]"

let mode_to_string m =
  match m with Concrete -> "C" | Symbolic -> "S" | Multivalue -> "M"

open ProbNv_datastructures
include ProbNv_utils.PrimitiveCollections
module VarMap = BetterMap.Make (Var)

let canonicalize_type (ty : ty) : ty =
  let rec aux ty map count =
    match ty.typ with
    | TBool | TInt _ | TNode | TEdge | TFloat -> (ty, map, count)
    | TArrow (t1, t2) ->
        let t1', map, count = aux t1 map count in
        let t2', map, count = aux t2 map count in
        ({ ty with typ = TArrow (t1', t2') }, map, count)
    | TTuple tys ->
        let tys', map, count =
          BatList.fold_left
            (fun (lst, map, count) t ->
              let t', map, count = aux t map count in
              (t' :: lst, map, count))
            ([], map, count) tys
        in
        ({ ty with typ = TTuple (BatList.rev tys') }, map, count)
    | TOption t ->
        let t', map, count = aux t map count in
        ({ ty with typ = TOption t' }, map, count)
    | TRecord tmap ->
        let open RecordUtils in
        let tmap', map, count =
          List.fold_left2
            (fun (tmap, map, count) l t ->
              let t', map, count = aux t map count in
              (StringMap.add l t' tmap, map, count))
            (StringMap.empty, map, count)
            (get_record_labels tmap) (get_record_entries tmap)
        in
        ({ ty with typ = TRecord tmap' }, map, count)
    | TMap (t1, t2) ->
        let t1', map, count = aux t1 map count in
        let t2', map, count = aux t2 map count in
        ({ ty with typ = TMap (t1', t2') }, map, count)
    | QVar tyname -> (
        match VarMap.Exceptionless.find tyname map with
        | None ->
            let new_var = Var.to_var ("a", count) in
            ( { ty with typ = QVar new_var },
              VarMap.add tyname new_var map,
              count + 1 )
        | Some v -> ({ ty with typ = QVar v }, map, count) )
    | TVar r -> (
        match !r with
        | Link t -> aux { t with mode = join_opts t.mode ty.mode } map count
        | Unbound _ -> (ty, map, count) )
  in
  let result, _, _ = aux ty VarMap.empty 0 in
  result

(* The way we print our types means that we don't really need precedence rules.
   The only type which isn't totally self-contained is TArrow *)
let rec base_ty_to_string ?(show_modes = true) t =
  match t with
  | TVar { contents = tv } -> tyvar_to_string tv
  | QVar name -> "{" ^ Var.to_string name ^ "}"
  (* | TUnit -> "unit" *)
  | TBool -> Printf.sprintf "bool"
  | TInt i -> Printf.sprintf "int%d" i
  | TNode -> Printf.sprintf "tnode"
  | TEdge -> Printf.sprintf "tedge"
  | TFloat -> "float"
  | TTuple ts ->
      if List.is_empty ts then "TEmptyTuple"
      else "(" ^ sep "," (ty_to_string ~show_modes) ts ^ ")"
  | TOption t -> "option[" ^ ty_to_string ~show_modes t ^ "]"
  | TMap (t1, t2) ->
      "dict["
      ^ ty_to_string ~show_modes t1
      ^ ","
      ^ ty_to_string ~show_modes t2
      ^ "]"
  | TRecord map -> print_record ":" ty_to_string map
  | TArrow (t1, t2) ->
      let leftside =
        match t1.typ with
        | TArrow _ -> Printf.sprintf "(%s)" (ty_to_string ~show_modes t1)
        | _ -> ty_to_string ~show_modes t1
      in
      Printf.sprintf "(%s -> %s)" leftside (ty_to_string ~show_modes t2)

and ty_to_string ?(show_modes = true) ty =
  (* let ty = canonicalize_type ty in *)
  if show_modes then
    match ty.mode with
    | None -> Printf.sprintf "[None]%s" (base_ty_to_string ~show_modes ty.typ)
    | Some m ->
        Printf.sprintf "[%s]%s" (mode_to_string m)
          (base_ty_to_string ~show_modes ty.typ)
  else Printf.sprintf "%s" (base_ty_to_string ~show_modes ty.typ)

and tyvar_to_string tv =
  match tv with
  | Unbound (name, l) -> Var.to_string name ^ "[" ^ string_of_int l ^ "]"
  | Link ty -> "<" ^ ty_to_string ty ^ ">"

let op_to_string op =
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | UAdd n -> "+" ^ "u" ^ string_of_int n
  | FAdd -> "+."
  | FDiv -> "/."
  | FMul -> "*."
  | UAnd n -> "&" ^ "u" ^ (string_of_int n)
  (* | USub n -> "-" ^ "u" ^ (string_of_int n)
      *)
  | Eq -> "="
  | ULess n -> "<" ^ "u" ^ string_of_int n
  | BddAnd -> "&&b"
  | BddUAnd _ -> "&b"
  | BddOr -> "||b"
  | BddAdd _ -> "+b"
  | BddNot -> "!b"
  | BddLess _ -> "<b"
  | BddLeq _ -> "<=b"
  | BddEq -> "=b"
  | ULeq n -> "<=" ^ "u" ^ string_of_int n
  | NLess -> "<n"
  | NLeq -> "<=n"
  | ELess -> "<e"
  | ELeq -> "<=e"
  | FLess -> "<."
  | FLeq -> "<=."
  | MCreate -> "createMap"
  | MGet -> "at"
  | MSet -> "set"
  | MMerge -> "combine"
  | MSize -> "size"
  | TGet (i, _) -> "get-" ^ string_of_int i

let rec pattern_to_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> Var.to_string x
  | PBool true -> "true"
  | PBool false -> "false"
  | PInt i -> Integer.to_string i
  | PFloat f -> string_of_float f
  | PTuple ps ->
      if List.is_empty ps then "PEmptyTuple"
      else "(" ^ comma_sep pattern_to_string ps ^ ")"
  | POption None -> "None"
  | POption (Some p) -> "Some " ^ pattern_to_string p
  | PRecord map -> print_record "=" pattern_to_string map
  | PNode n -> Printf.sprintf "%dn" n
  | PEdgeId n -> Printf.sprintf "%de" n
  | PEdge (p1, p2) ->
      Printf.sprintf "%s~%s" (pattern_to_string p1) (pattern_to_string p2)

let padding i = String.init i (fun _ -> ' ')

let ty_env_to_string env = Env.to_string ty_to_string env.ty

let tyo_to_string tyo =
  match tyo with None -> "None" | Some ty -> ty_to_string ty

let glob = ref false

let count_tops arr =
  let j = ref 0 in
  for i = 0 to Array.length arr - 1 do
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

let pick_default_value map =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
      let c = count_tops vars in
      if c > !count then count := c;
      value := Some v)
    map;
  OCamlUtils.oget !value

(* Basic version *)
(* : value list * value *)
(* let bindings (map : mtbdd) =
  let bs = ref [] in
  (* let dv = pick_default_value map in *)
  match map with
  | m, _ ->
      Mtbddc.iter_cube (fun k v -> bs := (k, v) :: !bs) m;
      !bs *)

let bindings (map : mtbdd) =
  match map with m, _ -> Array.to_list @@ Mtbddc.leaves m

let rec value_env_to_string ~show_types env =
  Env.to_string (value_to_string_p ~show_types max_prec) env.value

and env_to_string ?(show_types = false) env =
  if env.ty = Env.empty && env.value = Env.empty then " "
  else
    "[" ^ ty_env_to_string env ^ "|"
    ^ value_env_to_string ~show_types env
    ^ "] "

and func_to_string_p ~show_types prec { arg = x; argty; resty = _; body } =
  let s_arg = Var.to_string x in
  let arg_str =
    if show_types then Printf.sprintf "(%s : %s)" s_arg (tyo_to_string argty)
    else s_arg
  in
  let s =
    Printf.sprintf "fun %s -> %s " arg_str
      (exp_to_string_p ~show_types max_prec body)
  in
  if prec < max_prec then "(" ^ s ^ ")" else s

and closure_to_string_p ~show_types prec
    (env, { arg = x; argty = argt; resty = rest; body }) =
  let s_arg =
    match argt with
    | None -> Var.to_string x
    | Some t -> "(" ^ Var.to_string x ^ ":" ^ ty_to_string t ^ ")"
  in
  let s_res = match rest with None -> "" | Some t -> " : " ^ ty_to_string t in
  let s =
    "fun"
    ^ env_to_string ~show_types env
    ^ s_arg ^ s_res ^ " -> "
    ^ exp_to_string_p ~show_types prec body
  in
  if prec < max_prec then "(" ^ s ^ ")" else s

and value_to_string_p ~show_types prec v =
  let value_to_string_p = value_to_string_p ~show_types in
  match v.v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> Integer.to_string i
  | VFloat f -> Printf.sprintf "%.10f" f
  | VTotalMap (m, meta) -> (
      match meta with
      | None -> multivalue_to_string ~show_types "," m
      | Some (kty, range) -> map_to_string ~show_types ", " m kty range )
  | VTuple vs ->
      if List.is_empty vs then "VEmptyTuple"
      else "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
  | VOption None -> "None"
  | VOption (Some v) ->
      let s = "Some(" ^ value_to_string_p max_prec v ^ ")" in
      if max_prec > prec then "(" ^ s ^ ")" else s
  | VRecord map -> print_record "=" (value_to_string_p prec) map
  | VNode n -> Printf.sprintf "%dn" n
  | VEdge (EdgeId e) ->
      let u, v = PrimitiveCollections.IntMap.find e !edge_mapping in
      Printf.sprintf "%d-%d" u v
  | VEdge (Raw (u, v)) -> Printf.sprintf "%d-%d" u v
  | VClosure cl -> closure_to_string_p ~show_types prec cl

and map_to_string ~show_types term_s m kty range =
  let binding_to_string (k, v) =
    (* let key =
         Array.fold_right
           (fun x acc ->
             match x with
             | Man.True -> Printf.sprintf "1%s" acc
             | Man.False -> Printf.sprintf "0%s" acc
             | Man.Top -> Printf.sprintf "*%s" acc)
           k ""
       in *)
    Printf.sprintf "%s" (value_to_string_p ~show_types max_prec v)
    (* Printf.sprintf "%s |-> %s" key (value_to_string_p ~show_types max_prec v) *)
  in
  let bs = Array.to_list @@ Mtbddc.guardleafs m in
  Printf.sprintf "{ %s }" (term term_s binding_to_string bs)

and multivalue_to_string ~show_types term_s m =
  let bs = Array.to_list @@ Mtbddc.leaves m in
  term term_s
    (fun v -> Printf.sprintf " %s" (value_to_string_p ~show_types max_prec v))
    bs

(* and multivalue_to_string ~show_types term_s m =
  let binding_to_string (k, v) =
    (* BddMap.multiValue_to_string k *)
    value_to_string_p ~show_types max_prec k
    ^ " ~> "
    ^ value_to_string_p ~show_types max_prec v
  in
  let bs =
    bindingsOld (m, concrete (TTuple [ concrete TEdge; concrete TEdge ]))
  in
  match bs with
  | [] -> Printf.sprintf "{ _ |-> _ }"
  | _ -> Printf.sprintf "{ %s }" (term term_s binding_to_string bs) *)
and exp_to_string_p ~show_types prec e =
  let exp_to_string_p = exp_to_string_p ~show_types in
  let value_to_string_p = value_to_string_p ~show_types in
  let p = prec_exp e in
  let s =
    match e.e with
    | EVar x -> Var.name x
    | EVal v -> value_to_string_p prec v
    | EOp (op, es) -> op_args_to_string ~show_types prec p op es
    | EFun f -> func_to_string_p ~show_types prec f
    | EApp (e1, e2) ->
        exp_to_string_p prec e1 ^ " " ^ exp_to_string_p p e2 ^ " "
    | EIf (e1, e2, e3) ->
        "if "
        ^ exp_to_string_p max_prec e1
        ^ " then \n"
        ^ exp_to_string_p max_prec e2
        ^ " else \n" ^ exp_to_string_p prec e3
    | ELet (x, e1, e2) ->
        "let " ^ Var.to_string x ^ "="
        ^ exp_to_string_p max_prec e1
        ^ " in \n" ^ exp_to_string_p prec e2
    | EBddIf (e1, e2, e3) ->
        Printf.sprintf "bddIf %s then \n %s else %s \n"
          (exp_to_string_p max_prec e1)
          (exp_to_string_p max_prec e2)
          (exp_to_string_p max_prec e3)
    | EApplyN (e1, es) ->
        Printf.sprintf "applyN(%s, %s)"
          (exp_to_string_p max_prec e1)
          (comma_sep (exp_to_string_p max_prec) es)
    | EToBdd e1 -> Printf.sprintf "toBdd (%s)" (exp_to_string_p max_prec e1)
    | EToMap e1 -> Printf.sprintf "toMap (%s)" (exp_to_string_p max_prec e1)
    | ETuple es ->
        if List.is_empty es then "EEmptyTuple"
        else "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
    | EMatch (e1, bs) ->
        "(match "
        ^ exp_to_string_p max_prec e1
        ^ " with " ^ "\n"
        ^ branches_to_string ~show_types prec (branchToList bs)
        ^ ")"
    | ESome e -> "Some(" ^ exp_to_string_p prec e ^ ")"
    | ERecord map -> print_record "=" (exp_to_string_p prec) map
    | EProject (e, l) -> exp_to_string_p prec e ^ "." ^ l
  in

  if show_types then Printf.sprintf "(%s : %s)" s (tyo_to_string e.ety)
  else if p > prec then "(" ^ s ^ ")"
  else s

and branch_to_string ~show_types prec (p, e) =
  " | " ^ pattern_to_string p ^ " -> " ^ exp_to_string_p ~show_types prec e

and branches_to_string ~show_types prec bs =
  match bs with
  | [] -> ""
  | b :: bs ->
      branch_to_string ~show_types prec b
      ^ "\n"
      ^ branches_to_string ~show_types prec bs

and op_args_to_string ~show_types prec p op es =
  let exp_to_string_p = exp_to_string_p ~show_types in
  if is_keyword_op op then
    op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
  else
    match es with
    | [] -> op_to_string op ^ "()" (* should not happen *)
    | [ e1 ] -> op_to_string op ^ " " ^ exp_to_string_p p e1
    | [ e1; e2 ] ->
        exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " "
        ^ exp_to_string_p prec e2
    | es ->
        op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"

let value_to_string ?(show_types = false) v =
  value_to_string_p ~show_types max_prec v

let exp_to_string ?(show_types = false) e =
  exp_to_string_p ~show_types max_prec e

let func_to_string ?(show_types = false) f =
  func_to_string_p ~show_types max_prec f

let closure_to_string ?(show_types = false) c =
  closure_to_string_p ~show_types max_prec c

let rec distrExpr_to_string bs =
  match bs with
  | [] -> ""
  | b :: bs ->
      Printf.sprintf "%s\n%s" (distrBranch_to_string b) (distrExpr_to_string bs)

and distrPattern_to_string p =
  match p with
  | DistrPWild -> "_"
  | DistrPBool b -> if b then "true" else "false"
  | DistrPRange (a, b) ->
      Printf.sprintf "[%s, %s]" (Integer.to_string a) (Integer.to_string b)
  | DistrPNode n -> Printf.sprintf "%dn" n
  | DistrPEdge (n1, n2) -> Printf.sprintf "%d-%d" n1 n2
  | DistrPTuple ps -> "(" ^ comma_sep distrPattern_to_string ps ^ ")"

and distrBranch_to_string (pat, p) =
  " | " ^ distrPattern_to_string pat ^ " -> " ^ string_of_float p

(* TODO: should the let statements use the identifiers defined in Syntax instead? *)
let rec declaration_to_string ?(show_types = false) d =
  let exp_to_string = exp_to_string ~show_types in
  match d with
  | DLet (x, e, _) -> "let " ^ Var.to_string x ^ " = " ^ exp_to_string e ^ "\n"
  | DSymbolic (xs, ty, Uniform) ->
      Printf.sprintf "symbolic %s : %s" (Var.printVarList xs) (ty_to_string ty)
  | DSymbolic (xs, ty, DExpr dexp) ->
      Printf.sprintf "symbolic %s : %s = %s" (Var.printVarList xs)
        (ty_to_string ty) (distrExpr_to_string dexp)
  | DSymbolic (xs, ty, Expr dexp) ->
      Printf.sprintf "symbolic %s : %s = %s" (Var.printVarList xs)
        (ty_to_string ty) (exp_to_string dexp)
  | DInfer (name, e, cond) ->
      let condString =
        match cond with
        | None -> ""
        | Some cond -> Printf.sprintf " | %s" (exp_to_string cond)
      in
      Printf.sprintf "assert(%s, %s%s)" name (exp_to_string e) condString
  | DSolve { aty; var_names; init; trans; merge } ->
      Printf.sprintf
        "let %s = solution<%s> {init = %s; trans = %s; merge = %s}\n"
        (exp_to_string var_names)
        (match aty with None -> "None" | Some ty -> ty_to_string ty)
        (exp_to_string init) (exp_to_string trans) (exp_to_string merge)
  | DForward
      { names_V; names_E; fwdInit; fwdOut; fwdIn; hinitV; hinitE; logE; logV }
    ->
      Printf.sprintf "let (%s, %s) = forward(%s, %s, %s, %s, %s, %s, %s)\n"
        (exp_to_string names_V) (exp_to_string names_E) (exp_to_string fwdInit)
        (exp_to_string fwdOut) (exp_to_string fwdIn) (exp_to_string hinitV)
        (exp_to_string hinitE) (exp_to_string logV) (exp_to_string logE)
  | DNodes (n, xs) ->
      "let nodes = " ^ string_of_int n
      ^ List.fold_right (fun (u, r) s -> Printf.sprintf "%s%d: %s;" s u r) xs ""
      ^ "}"
  | DEdges es ->
      "let edges = {"
      ^ List.fold_right
          (fun (u, v, i) s -> Printf.sprintf "%s(%dn-%dn, %d);" s u v i)
          es ""
      ^ "}"
  | DUserTy (name, ty) ->
      Printf.sprintf "type %s = %s" (Var.to_string name) (ty_to_string ty)

let rec declarations_to_string ?(show_types = false) ds =
  match ds with
  | [] -> ""
  | d :: ds ->
      declaration_to_string ~show_types d
      ^ "\n"
      ^ declarations_to_string ~show_types ds

let rec printSvalue sv =
  match sv with
  | SBool FullSet | SNode FullSet | SEdge FullSet | SInt FullSet -> "*"
  | SBool (Subset b) -> Printf.sprintf "%b" b
  | SInt (Subset is) ->
      PrimitiveCollections.printList
        (fun i -> Integer.to_string i)
        is "{" "," "}"
  | SNode (Subset ns) ->
      PrimitiveCollections.printList (fun i -> string_of_int i) ns "{" "," "}"
  | SEdge (Subset es) ->
      PrimitiveCollections.printList
        (fun (u, v) -> Printf.sprintf "%d~%d" u v)
        es "{" "," "}"
  | STuple svs ->
      PrimitiveCollections.printList (fun sv -> printSvalue sv) svs "(" "," ")"
