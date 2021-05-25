open ANSITerminal
open ProbNv_datastructures
open ProbNv_lang
open ProbNv_lang.Cmdline
open ProbNv_lang.Syntax
open ProbNv_transformations
open ProbNv_utils
open ProbNv_translate
open ProbNv_compile
open ProbNv_solution
open OCamlUtils

type answer = Success of Solution.t option | CounterExample of Solution.t

let rec apply_all (s : Solution.t) fs =
  match fs with [] -> s | f :: fs -> apply_all (f s) fs

(** Native simulator - compiles SRP to OCaml *)
let run_compiled file _ _ decls topology fs =
  let path = Filename.remove_extension file in
  let name = Filename.basename path in
  let name =
    String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) name
  in
  let newpath = name in
  let nodeNames = !node_mapping in
  let solution =
    apply_all (Loader.simulate nodeNames topology newpath decls) fs
  in
  Solution.print_solution solution

let parse_input (args : string array) =
  let cfg, rest = argparse default "probNV" args in
  Cmdline.set_cfg cfg;
  let cfg = Cmdline.get_cfg () in
  BddUtils.set_reordering cfg.reordering;
  if cfg.debug then Printexc.record_backtrace true;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  (* Parse probNV file *)
  let decls = ds in
  let nodes = get_nodes decls |> ProbNv_utils.OCamlUtils.oget in
  let edges = get_edges decls |> ProbNv_utils.OCamlUtils.oget in
  let topology = AdjGraph.create (fst nodes) edges in
  (* Type check the HLL program *)
  let decls = ToEdge.toEdge_decl topology :: decls in
  create_topology_mapping (snd nodes) topology;
  let decls = Typing.HLLTypeInf.infer_declarations info decls in
  let decls, f = RecordUnrolling.unroll_declarations decls in
  let fs = [ f ] in
  (* Note! Must rename before inling otherwise inling is unsound *)
  let decls, f = Renaming.alpha_convert_declarations decls in
  (* Printf.printf "Printing type checked program\n\n%s\n\n"
     (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls); *)
  let fs = f :: fs in
  (* inlining definitions *)
  let decls =
    if cfg.inline then
      Profile.time_profile "Inlining all" (fun () ->
          Inline.inline_declarations decls)
    else
      Profile.time_profile "Inlining Multivalues" (fun () ->
          Inline.inline_multivalue_declarations decls)
  in
  (* Printf.printf "Printing inlined program\n\n%s\n\n"
     (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls); *)
  (* Translate the program to LLL *)
  let decls = Translate.translate_declarations info decls in
  (* Printf.printf "Printing translated program\n\n%s"
     (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls); *)
  (* Type check the LLL program *)
  (* Printf.printf "LLL type checking after translation \n"; *)
  let decls = Typing.LLLTypeInf.infer_declarations info decls in
  let decls, _ = EdgeTransformer.edge_transformer topology decls in
  let decls = ToEdge.fromEdge_decl topology :: decls in
  (* Printf.printf "done type checking and translating \n"; *)
  (cfg, info, file, decls, topology, fs)
