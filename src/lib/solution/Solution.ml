open ANSITerminal
open ProbNv_datastructures
open ProbNv_lang
open Collections
open AdjGraph (* For VertexMap *)
open Syntax
open ProbNv_utils
open OCamlUtils

type sol = {sol_val: value AdjGraph.VertexMap.t ; attr_ty: Syntax.ty}
type t =
  { solves: (var * sol) list;
    assertions: bool list; (* One for each assert statement *)
    nodes: int;
  }

type map_back = t -> t

let print_fun nodes {sol_val} =
  let solString = ref [] in
  let f = fun x -> Printing.value_to_string ~show_types:false x in
  for i=(nodes-1) downto 0 do
    let v = AdjGraph.VertexMap.find i sol_val in
    solString := (i, f v) :: !solString
  done;
  PrimitiveCollections.printList (fun (u,s) -> Printf.sprintf "Node %d\n---------\n%s" u s) !solString "" "\n\n" "\n"

let print_solution (solution : t) =
  let cfg = ProbNv_lang.Cmdline.get_cfg () in
  print_newline () ;
  if cfg.verbose then
    begin
      (* Print solutions*)
      List.iter (fun (k,v) ->
          Printf.printf "Printing solutions for %s\n" (Var.to_string k);
          print_endline (print_fun solution.nodes v)) solution.solves
    end;
  ( match solution.assertions with
    | [] ->
      print_string [green; Bold] "Success: " ;
      Printf.printf "No assertions provided, so none failed\n"
    | asns ->
      let all_pass = List.for_all (fun x -> x) asns in
      if all_pass then (
        print_string [green; Bold] "Success: " ;
        Printf.printf "all assertions passed\n" )
      else
        (print_string [red; Bold] "Failed: " ;
         asns
         |> BatList.mapi (fun i b -> Printf.sprintf "Assertion %d" i, b)
         |> BatList.filter_map (fun (s, b) -> if not b then Some s else None)
         |> BatString.concat ", "
         |> print_endline))
      ;
      print_newline ()
