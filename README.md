# Probabilistic Network Verification


## Building ProbNV

To start with, make sure you have all of these dependencies: `gcc, make, m4` for `ocaml`, `g++` for `mlcuddidl` and `libgmp` for zarith.
Use `opam` to install the `ocaml` dependencies.

If you don't have `opam` yet, see the [OPAM install instructions](https://opam.ocaml.org/doc/Install.html).
This is the best way to set up `ocaml`.

Once you've installed dune using `opam install dune`, you can see which `ocaml` packages you're missing to run `ProbNV` using:

```
dune external-lib-deps --missing @all
```

Alternatively, execute the following to install required packages once `opam` is up:

```
opam install -y \
  integers \
  batteries \
  ounit \
  ansiterminal \
  menhir \
  mlcuddidl \
  ppx_deriving \
  ppx_deriving_argparse \
  zarith \
  ocamlgraph \
  fileutils \
  dune
```

Then clone the repo and run `make; dune build; dune install`.

## Getting started with ProbNV

Folder examples contains example networks, including the ones that were used in the paper. For example, to compute the stable state of the BICS network and verify reachability under all node failures, execute the following command in your shell:

```
./probNv examples/BICS/bics_nodeFaults_bfs.n
```

The `-verbose` option prints the stable state (solutions) for each node.
Use `-new-sim` to enable the new simulation algorithm and `-sim-skip K` to configure how many dependencies it may skip during processing.
```
