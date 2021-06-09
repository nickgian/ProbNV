type t = {
  debug : bool; [@short "-d"]  (** enable a debugging backtrace            *)
  verbose : bool; [@short "-v"]  (** print out the srp solution              *)
  bound : int option;  (** bound the number of simulation steps    *)
  memoize : bool; [@short "-z"]  (** memoizes the interpreter for reuse      *)
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
}
[@@deriving
  show,
    argparse
      {
        positional = [ ("file", "probNV file") ];
        description = "nv: a network verification framework";
      }]

let default =
  {
    debug = false;
    verbose = false;
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
  }

let cfg = ref default

let get_cfg () = !cfg

let set_cfg c = cfg := c
