
type t =
  { debug: bool       [@short "-d"]    (** enable a debugging backtrace            *)
  ; verbose: bool     [@short "-v"]    (** print out the srp solution              *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; memoize: bool     [@short "-z"]    (** memoizes the interpreter for reuse      *)
  ; no_caching: bool                   (** disables mtbdd operation caching        *)
  ; no_cutoff: bool                    (** disables mtbdd early termination        *)
  (*; compile: bool                      (** compile network to OCaml code before simulation *)*)
  }
[@@deriving
  show
  , argparse
      { positional= [("file", "probNV file")]
      ; description= "nv: a network verification framework" }]

let default =
  { debug = false
  ; verbose = false
  ; bound = None
  ; memoize = false
  ; no_caching = false
  ; no_cutoff = false
  (* ; compile=false *)
  }

let cfg = ref default

let get_cfg () = !cfg

let set_cfg c = cfg := c
