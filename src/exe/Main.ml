open ProbNv.Main_defs

let main_func () =
  Printexc.record_backtrace true;
  let cfg, info, file, decls, fs = parse_input Sys.argv in
  Printf.printf "Printing compiled program\n\n%s"
    (ProbNv_lang.Printing.declarations_to_string ~show_types:true decls)

let main = ProbNv_utils.Profile.time_profile_absolute "Entire Program" main_func
