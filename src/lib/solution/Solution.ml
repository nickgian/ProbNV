open ANSITerminal
open ProbNv_datastructures
open ProbNv_lang
open Collections
open AdjGraph (* For VertexMap *)

open Syntax
open ProbNv_utils
open OCamlUtils

type sol = { sol_val : value AdjGraph.VertexMap.t; attr_ty : Syntax.ty }

type t = {
  solves : (var * sol) list;
  assertions : (string * bool * float) list;
  (* One for each assert statement *)
  nodes : int * string IntMap.t;
}

type map_back = t -> t

let print_fun nodes { sol_val } =
  let solString = ref [] in
  let f x = Printing.value_to_string ~show_types:false x in
  let numNodes = fst nodes in 
  let nodeNames = snd nodes in
  for i = numNodes - 1 downto 0 do
    let v = AdjGraph.VertexMap.find i sol_val in
    let istr = match IntMap.find_opt i nodeNames with | None -> "" | Some str -> str in
    solString := (i, istr, f v) :: !solString
  done;
  PrimitiveCollections.printList
    (fun (u, ustr,  s) -> Printf.sprintf "Node %s (%d)\n---------\n%s" ustr u s)
    !solString "" "\n\n" "\n"

let print_solution (solution : t) =
  let cfg = ProbNv_lang.Cmdline.get_cfg () in
  print_newline ();
  if cfg.verbose then
    (* Print solutions*)
    List.iter
      (fun (k, v) ->
        Printf.printf "Printing solutions for %s\n" (Var.to_string k);
        print_endline (print_fun solution.nodes v))
      solution.solves;
  match solution.assertions with
  | [] ->
      print_string [ green; Bold ] "Success: ";
      Printf.printf "No assertions provided, so none failed\n"
  | asns ->
      let all_pass = List.for_all (fun (_, x, _) -> x) asns in
      if all_pass then (
        print_string [ green; Bold ] "Success: ";
        Printf.printf "all assertions passed\n" )
      else
        print_string [ red; Bold ]
          "Failed. Here are more details about the computed assertions:\n ";
      Printf.printf "%s"
        (Collections.printListi
           (fun i (name, b, p) ->
             Printf.sprintf
               "Assertion %s (%d) %s. It returned true with probability %f" name i
               (if b then "succeeded" else "failed")
               p)
           asns "" "\n" "\n")
