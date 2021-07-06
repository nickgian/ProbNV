open ProbNv.Main_defs

let main_func () =
  Printexc.record_backtrace true;
  let cfg, info, file, decls, topology, fs = parse_input Sys.argv in
  run_compiled file cfg info decls topology fs

let main =
  let () =
    Gc.set
      {
        (Gc.get ()) with
        Gc.minor_heap_size = 8388608;
        Gc.major_heap_increment = 1000;
        Gc.space_overhead = 80;
        Gc.allocation_policy = 2 (* Gc.max_overhead = 2000000; *);
      }
  in
  ProbNv_utils.Profile.time_profile_absolute "Entire Program" main_func
