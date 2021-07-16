open ANSITerminal
open ProbNv_datastructures
open ProbNv_lang
open Collections
open AdjGraph (* For VertexMap *)

open Syntax
open ProbNv_utils
open OCamlUtils

type sol = { sol_val : value AdjGraph.VertexMap.t; attr_ty : Syntax.ty }

type 'a forwardSolutions = {
  hvName : string;
  heName : string;
  historyV : 'a AdjGraph.VertexMap.t;
  historyE : 'a AdjGraph.EdgeMap.t;
  historyV_ty : Syntax.ty;
  historyE_ty : Syntax.ty;
}

type t = {
  solves : (var * sol) list;
  forwarding : value forwardSolutions list;
  (* One for each assert statement: name, probability assertion holds, and list of counterexamples *)
  assertions : (string * float * svalue Collections.StringMap.t list) list;
  (* Name of variable and NV value *) 
  values : (string * value) list; 
  nodes : int * string IntMap.t;
}

type map_back = t -> t

let print_fun_node nodes sol_val =
  let solString = ref [] in
  let f x = Printing.value_to_string ~show_types:false x in
  let numNodes = fst nodes in
  let nodeNames = snd nodes in
  for i = numNodes - 1 downto 0 do
      match AdjGraph.VertexMap.find_opt i sol_val with
      | None -> ()
      | Some v -> 
        let istr =
          match IntMap.find_opt i nodeNames with None -> "" | Some str -> str
        in
        solString := (i, istr, f v) :: !solString
  done;
  PrimitiveCollections.printList
    (fun (u, ustr, s) -> Printf.sprintf "Node %s (%d)\n---------\n%s" ustr u s)
    !solString "" "\n\n" "\n"

let print_fun_edge nodes vals =
  let f x = Printing.value_to_string ~show_types:false x in
  let nodeNames = snd nodes in
  let buf = Buffer.create 500 in
  AdjGraph.EdgeMap.iter
    (fun e value ->
      let u, v = (AdjGraph.Edge.src e, AdjGraph.Edge.dst e) in
      let ustr =
        match IntMap.find_opt u nodeNames with None -> "" | Some str -> str
      in
      let vstr =
        match IntMap.find_opt v nodeNames with None -> "" | Some str -> str
      in
      let uvstr = if ustr = "" && vstr = "" then "" else ustr ^ " - " ^ vstr in
      Buffer.add_string buf
        (Printf.sprintf "Edge %s (%d-%d)\n---------\n%s\n\n" uvstr u v
           (f value)))
    vals;
  Buffer.contents buf

(* Helper functions to print counterexamples *)
let printCounterExample counterExample =
  Collections.StringMap.fold
    (fun var sval acc ->
      Printf.sprintf "%s, %s = %s" acc var (Printing.printSvalue sval))
    counterExample ""

let printCounterExamples counterExamples =
  Collections.printList
    (fun cube -> printCounterExample cube)
    counterExamples "" "\n" "\n"

let printValues values = 
  List.iter
    (fun (name, v) -> Printf.printf "%s,%s\n" name (Printing.value_to_string v)) values

let print_solution (solution : t) =
  let cfg = ProbNv_lang.Cmdline.get_cfg () in
  print_newline ();
  if cfg.verbose = 2 then (
    (* Print solutions*)
    List.iter
      (fun (k, v) ->
        Printf.printf "Printing solutions for %s\n" (Var.to_string k);
        print_endline (print_fun_node solution.nodes v.sol_val))
      solution.solves;
    (* Print forwarding *)
    List.iter
      (fun f ->
        Printf.printf "Printing forwarding histories for %s, %s\n" f.hvName
          f.heName;
        print_endline (print_fun_node solution.nodes f.historyV);
        print_endline (print_fun_edge solution.nodes f.historyE))
      solution.forwarding;
    (* Print let values *)
    printValues solution.values  
      )
  else if cfg.verbose = 1 then
    (* Print let values *)
    printValues solution.values;
  match solution.assertions with
  | [] -> Printf.printf "No assertions provided\n"
  | asns ->
      Printf.printf "%s"
        (Collections.printListi
           (fun i (name, p, counterExamples) ->
             let s =
               Printf.sprintf
                 "Assertion %s (%d) returned true with probability %.10f" name i
                 p
             in
             if cfg.counterexample && p != 1.0 then
               Printf.sprintf "%s\nCounterexamples:\n----------------\n%s" s
                 (printCounterExamples counterExamples)
             else s)
           asns "" "\n" "\n")

(** ** CSV printing *)

let toCSV_fun_node name nodes sol_val =
  let solString = ref [] in
  let f x = Printing.value_to_string ~show_types:false x in
  let numNodes = fst nodes in
  let nodeNames = snd nodes in
  for i = numNodes - 1 downto 0 do
    let v = AdjGraph.VertexMap.find i sol_val in
    let istr =
      match IntMap.find_opt i nodeNames with None -> "" | Some str -> str
    in
    solString := (i, istr, f v) :: !solString
  done;
  PrimitiveCollections.printList
    (fun (u, ustr, s) -> Printf.sprintf "%s, %d,%s,%s" name u ustr s)
    !solString "" "\n\n" "\n"

let toCSV_fun_edge nodes vals =
  let f x = Printing.value_to_string ~show_types:false x in
  let nodeNames = snd nodes in
  let buf = Buffer.create 500 in
  AdjGraph.EdgeMap.iter
    (fun e value ->
      let u, v = (AdjGraph.Edge.src e, AdjGraph.Edge.dst e) in
      let elbl = AdjGraph.Edge.label e in
      let ustr =
        match IntMap.find_opt u nodeNames with None -> "" | Some str -> str
      in
      let vstr =
        match IntMap.find_opt v nodeNames with None -> "" | Some str -> str
      in
      let uvstr = if ustr = "" && vstr = "" then "" else ustr ^ " - " ^ vstr in
      Buffer.add_string buf
        (Printf.sprintf "%d,%s,%s\n" elbl uvstr (f value)))
    vals;
  Buffer.contents buf

let toCSV_values values = 
  PrimitiveCollections.printList (fun (name, v) ->
    Printf.sprintf "%s,%s" name (Printing.value_to_string v)) values "" "\n" "\n"

(* TODO: find a way to present counterexamples *)
let toCSV dir (solution : t) = 
  let cfg = ProbNv_lang.Cmdline.get_cfg () in
  let routesFile = open_out (dir ^ "/routes.csv") in
  let valuesFile = open_out (dir ^ "/values.csv") in
  if cfg.verbose = 2 then (
    (* Extract solutions*)
    List.iter
      (fun (k, v) ->
        Printf.fprintf routesFile "%s" (toCSV_fun_node (Var.name k) solution.nodes v.sol_val))
      solution.solves;
    (* TODO: extract forwarding histories to CSV, not high priority. *) 
   )
  else if cfg.verbose = 1 then
    (* Extract let-values *)
    Printf.fprintf valuesFile "%s" (toCSV_values solution.values);
  match solution.assertions with
  | [] -> ()
  | asns ->
      let assertionsFile = open_out (dir ^ "/assertions.csv") in
      Printf.fprintf assertionsFile "%s"
        (Collections.printList
           (fun (name, p, counterExamples) ->
             let s =
               Printf.sprintf
                 "%s,%.10f" name p
             in
             s
             (* if cfg.counterexample && p != 1.0 then
               Printf.sprintf "%s\nCounterexamples:\n----------------\n%s" s
                 (printCounterExamples counterExamples)
             else s) *)
           )
           asns "" "\n" "\n")

(* TODO: extracting counterexamples (should be easy but I can improve presentation and performance)
  How to get routes? large maps are difficult to print in their entirety.
  Can we instead have a small query language that runs in an interactive mode and returns results
  as requested?
  
  q ::=
  | get_solution(sol, node)
  | restrict q (expr : symbolic)
  | print q

*)