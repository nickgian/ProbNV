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
  assertions : (string * float) list;
  (* One for each assert statement, name * probability assertion holds *)
  nodes : int * string IntMap.t;
}

type map_back = t -> t

let print_fun_node nodes sol_val =
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

let print_solution (solution : t) =
  let cfg = ProbNv_lang.Cmdline.get_cfg () in
  print_newline ();
  if cfg.verbose then (
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
      solution.forwarding );
  match solution.assertions with
  | [] -> Printf.printf "No assertions provided\n"
  | asns ->
      Printf.printf "%s"
        (Collections.printListi
           (fun i (name, p) ->
             Printf.sprintf
               "Assertion %s (%d) returned true with probability %f" name i p)
           asns "" "\n" "\n")
