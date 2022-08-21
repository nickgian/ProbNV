type t = {
  debug : bool;  (** enable a debugging backtrace            *)
  verbose : int;  (** verbosity level, 0 prints only the assertion result(default), 1 additionally prints let-bound values annotated with "@log", 2 additionally prints SRP and forwarding solutions  *)
  bound : int option;  (** bound the number of simulation steps    *)
  memoize : bool;  (** memoizes the interpreter for reuse      *)
  no_caching : bool;  (** disables mtbdd operation caching        *)
  no_cutoff : bool;  (** disables mtbdd early termination        *)
  inline : bool;  (** inline all expressions                  *)
  reordering : int option;
      (** dynamic reordering technique to use: default is disabled, 0 for WINDOW_2, 1 for WINDOW_2_CONV, 2 for WINDOW_3, 3 for WINDOW_3_CONV, 4 for WINDOW_4, 5 for SIFT, 6 for SIFT_CONV*)
  new_sim : bool;  (** enables the new simulator based on dependecies. *)
  sim_skip : int;
      (** how many dependencies to skip, only applies to the new simulator.*)
  counterexample : bool;
      (** generate counterexamples for non-true assertions. *)
  nostats : bool;  (** Do not print computation time statistics *)
  csv : bool; (*generate output in CSV files instead of printing on stdout.*)
  input: string;
}
(* [@@deriving
  show,
    argparse
      {
        positional = [ ("file", "probNV file") ];
        description = "nv: a network verification framework";
      }] *)

let default =
  {
    debug = false;
    verbose = 0;
    bound = None;
    memoize = false;
    no_caching = false;
    no_cutoff = false;
    inline = false;
    reordering = None;
    new_sim = false;
    sim_skip = 1;
    counterexample = false;
    nostats = false;
    csv = false;
    input = "";
  }

let cfg = ref default

let () =
  Clap.description "nv: a network verification framework";

  let verbose = Clap.default_int ~long: "verbose" ~short:'v' 0 in
  let debug = Clap.flag ~set_long: "debug" ~set_short: 'd' false in
  let new_sim = Clap.flag ~set_long: "new-sim" false in
  let sim_skip = Clap.default_int ~long: "sim-skip" 0 in
  let counterexample = Clap.flag ~set_long: "counterexample" false in 
  let nostats = Clap.flag ~set_long: "nostats" false in 
  let csv = Clap.flag ~set_long: "csv" ~set_short: 'c' false in 
  let input_file = Clap.mandatory_string ~placeholder: "input" () in
  Clap.close();
  cfg := {!cfg with debug; verbose; new_sim; sim_skip; counterexample; nostats; csv; input=input_file}


let get_cfg () = !cfg

let set_cfg c = cfg := c
