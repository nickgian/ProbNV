open ANSITerminal
open ProbNv_datastructures
open ProbNv_lang
open ProbNv_lang.Cmdline
open ProbNv_lang.Syntax
open ProbNv_transformations
open ProbNv_utils
open OCamlUtils

(* type answer =
  | Success of (Solution.t option)
  | CounterExample of Solution.t

let rec apply_all (s : Solution.t) fs =
  match fs with
  | [] -> s
  | f :: fs -> apply_all (f s) fs *)

(* let run_simulator cfg _ decls fs =
  let decls, _ = OptimizeBranches.optimize_declarations decls in
  try
    let solution, q =
      match cfg.bound with
      | None ->
        (Profile.time_profile "Interpreted simulation"
           (fun () -> Simulator.simulate_declarations ~throw_requires:true decls)
        , QueueSet.empty Pervasives.compare )
      | Some b -> ignore b; failwith "Don't know what this means" (* Srp.simulate_net_bound net b *)
    in
    ( match QueueSet.pop q with
      | None -> ()
      | Some _ ->
        print_string [] "non-quiescent nodes:" ;
        QueueSet.iter
          (fun q ->
             print_string [] (string_of_int q ^ ";") )
          q ;
        print_newline () ;
        print_newline () ;
    );
    match solution.assertions with
    | [] -> Success (Some solution), fs
    | lst ->
      if List.for_all (fun b -> b) lst then
        Success (Some solution), fs
      else
        CounterExample solution, fs
  with Srp.Require_false ->
    Console.error "required conditions not satisfied" *)


let parse_input (args : string array) =
  let cfg, rest = argparse default "probNV" args in
  Cmdline.set_cfg cfg ;
  let cfg = Cmdline.get_cfg () in
  if cfg.debug then Printexc.record_backtrace true ;
  let file = rest.(0) in
  let ds, info = Input.parse file in (* Parse probNV file *)
  let decls = ds in
  let fs = () in
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
