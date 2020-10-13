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

let rec apply_all (s : Solution.t) fs = match fs with [] -> s | f :: fs -> apply_all (f s) fs

(** Native simulator - compiles SRP to OCaml *)
let run_compiled file _ _ decls fs =
  let path = Filename.remove_extension file in
  let name = Filename.basename path in
  let name = String.mapi (fun i c -> if i = 0 then Char.uppercase_ascii c else c) name in
  let newpath = name in
  let solution = Loader.simulate newpath decls in
  match solution.assertions with
  | [] -> (Success (Some solution), fs)
  | lst ->
      if List.for_all (fun b -> b) lst then (Success (Some solution), fs)
      else (CounterExample solution, fs)

let parse_input (args : string array) =
  let cfg, rest = argparse default "probNV" args in
  Cmdline.set_cfg cfg;
  let cfg = Cmdline.get_cfg () in
  if cfg.debug then Printexc.record_backtrace true;
  let file = rest.(0) in
  let ds, info = Input.parse file in
  (* Parse probNV file *)
  let decls = ds in
  let fs = [] in
  (* Type check the HLL program *)
  let decls = Typing.HLLTypeInf.infer_declarations info decls in
  (* Note! Must rename before inling otherwise inling is unsound *)
  let decls, f = Renaming.alpha_convert_declarations decls in
  let fs = f :: fs in
  (* inlining definitions *)
  let decls =
    if cfg.inline then
      Profile.time_profile "Inlining all" (fun () -> Inline.inline_declarations decls)
    else
      Profile.time_profile "Inlining Multivalues" (fun () ->
          Inline.inline_multivalue_declarations decls)
  in
  Printf.printf "Printing inlined program\n\n%s\n\n"
    (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls);
  (* Translate the program to LLL *)
  let decls = Translate.translate_declarations decls in
  Printf.printf "Printing compiled program\n\n%s"
    (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls);
  (* Type check the LLL program *)
  let decls = Typing.LLLTypeInf.infer_declarations info decls in
  (cfg, info, file, decls, fs)

(* print_endline @@ Printing.declarations_to_string decls ; *)
(* let decls = (ToEdge.toEdge_decl decls) :: decls in *)
(* let decls = Typing.infer_declarations info decls in *)
(* Typing.check_annot_decls decls ;
   Wellformed.check info decls ; *)
(* let decls, f = RecordUnrolling.unroll_declarations decls in
   let fs = [f] in *)
(* let decls,fs = (* inlining definitions *)
   if cfg.inline then
     (* Note! Must rename before inling otherwise inling is unsound *)
     let decls, f = Renaming.alpha_convert_declarations decls in
     (Profile.time_profile "Inlining" (
         fun () ->
           Inline.inline_declarations decls |>
           (* TODO: We could probably propagate type information through inlining *)
           Typing.infer_declarations info), f :: fs)
   else
     (decls,fs) *)
