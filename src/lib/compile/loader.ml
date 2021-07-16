open SrpNative
open Findlib
open Fl_dynload
open ProbNv_utils
open CompileBDDs
open ProbNv_datastructures
open ProbNv_lang
open Syntax
open OCamlUtils

let load_srp name =
  let () = Findlib.init () in
  try Fl_dynload.load_packages [ name ]
  with Dynlink.Error err -> Printf.printf "%s\n" (Dynlink.error_message err)

let simulate nodeNames topology name decls =
  (* Compile the program to OCaml *)
  ignore (Compile.compile_ocaml name decls);
  (* Load compiled program *)
  load_srp (name ^ ".plugin");

  (* Build the topology *)
  let module G : Topology = struct
    let graph = topology
  end in
  (* build bdd and type arrays so that lookups during execution will work *)
  Collections.TypeIds.seal type_store;
  Collections.DistrIds.seal distr_store;

  (*TODO: is this still relevant? *)
  Collections.ExpIds.seal pred_store;

  (* Build a simulator for SRPs *)
  let module SrpSimulator = ( val if (Cmdline.get_cfg ()).new_sim then
                                    (module SrpLazySimulation (G))
                                  else (module SrpSimulation (G))
                                : SrpSimulationSig )
  in
  (* Load compiled NV program*)
  let module CompleteSRP = (val get_srp ()) in
  (* Plug everything together to simulate the SRPs - this is where simulation occurs*)
  (* Doing the time profiling manually because I don't know how to make it work with modules *)
  let cfg = Cmdline.get_cfg () in

  let module Srp = (val (module CompleteSRP (SrpSimulator)) : NATIVE_SRP) in
  if cfg.nostats then ()
  else (
    Printf.printf "Number of nodes/edges in topology: %d/%d\n\n" (AdjGraph.nb_vertex G.graph) (AdjGraph.nb_edges G.graph);
    RouteComputationStats.printTotalSimulationStats ();
    ForwardingStats.printTotalSimulationStats ();
    Printf.printf "Time to compute the assertions: %f\n" !SrpSimulator.assertionTime;
    BddUtils.get_statistics () );
  (* Get the computed solutions *)
  build_solutions
    nodeNames
    topology
    Srp.record_fns
    !SrpSimulator.forwarding_solutions
    !SrpSimulator.solved !SrpSimulator.assertions !SrpSimulator.letValues
