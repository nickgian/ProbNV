open ProbNv.Main_defs

let main_func () =
  Printexc.record_backtrace true;
  let cfg, info, file, decls, fs = parse_input Sys.argv in
  run_compiled file cfg info decls fs

let main = ProbNv_utils.Profile.time_profile_absolute "Entire Program" main_func
