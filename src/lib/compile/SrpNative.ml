(** Simulates an SRP compiled to a native OCaml progam *)

open ProbNv_utils
open Unsigned
open ProbNv_solution
open ProbNv_lang
open ProbNv_datastructures
open ProbNv_lang.Collections
open Cudd

(** Type of SRP network *)
module type NATIVE_SRP = sig
  val record_fns : int * int -> 'a -> 'b
  (** Communication between SRPs and ProbNV *)

  val record_cnstrs : int -> 'c
end

(** Simulator signature*)
module type SrpSimulationSig = sig
  val simulate_solve :
    (int * int -> 'a -> 'b) ->
    (* record_fns *)
    int ->
    (* attribute type id *)
    string ->
    (* name of solution variable *)
    (int -> 'a) ->
    (* init function *)
    (int -> 'a -> 'a) ->
    (*transfer function, int argument is the edge id *)
    (int -> 'a -> 'a -> 'a) ->
    (* merge function *)
    'a CompileBDDs.t
  (** Takes as input record_fns, the attribute type id, the name of the
     variable storing the solutions, the init trans and merge functions and
     computes the solutions.*)

  type packet

  type hV

  type hE

  val simulate_forwarding :
    (int * int -> 'a -> 'b) ->
    (* record_fns *)
    string ->
    (* node history name *)
    string ->
    (* edge history name *)
    int ->
    (* vertex history type id *)
    int ->
    (* edge history type id *)
    (int -> packet) ->
    (* fwdInit function *)
    (int -> packet -> packet) ->
    (*fwdOut function, int argument is the edge id *)
    (int -> packet -> packet) ->
    (*fwdOut function, int argument is the edge id *)
    (int -> hV) ->
    (* hinitV function - int is the node id*)
    (int -> hE) ->
    (* hinitE function - int is the edge id *)
    (int -> packet -> hV -> hV) ->
    (* logV function - int is the node id*)
    (int -> packet -> hE -> hE) ->
    (* logE function - int is the edge id*)
    packet ->
    (* bot *)
    hV CompileBDDs.t * hE CompileBDDs.t

  val graph : AdjGraph.t

  val solved : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list ref
  (** List of solutions, each entry is the name of the SRP, a map from nodes to solutions, and the type of routes *)

  type forwardSolutions = unit Solution.forwardSolutions

  val forwarding_solutions : forwardSolutions list ref
  (** List of dataplane solutions, each entry is the name of the the history
    variables, a map from nodes to node histories, a map from edges to edge
    histories and the types of histories *)

  val assertions : (string * bool Mtbddc.t * BddFunc.t option) list ref
  (** List of assertions. We compute the probability they hold. *)

  (*TODO: maybe make it a variant to distinguish between a boolean and an Mtbdd boolean. *)
end

(** To complete the SRPs we need to add a simulator*)
module type CompleteSRPSig = functor (SIM : SrpSimulationSig) -> NATIVE_SRP

(** Reference to a NATIVE_SRP module *)
let (srp : (module CompleteSRPSig) option ref) = ref None

(** Getter function for [srp]*)
let get_srp () =
  match !srp with Some srp -> srp | None -> failwith "No srp loaded"

(******************)
(* SRP Simulator *)
(******************)

module type Topology = sig
  val graph : AdjGraph.t
end

module ForwardingSimulation (G : Topology) = struct
  type packet = unit Mtbddc.t (*placeholder *)

  type hV = unit

  type hE = unit

  (* Keeping track of the history of each node *)
  type historyV = hV AdjGraph.VertexMap.t

  (* Keeping track of the history of each link *)
  type historyE = hE AdjGraph.EdgeMap.t

  (* Current state of each switch/node *)
  type switchState = packet list AdjGraph.VertexMap.t

  (* Current state of each interface/link *)
  type interfaceState = packet list AdjGraph.EdgeMap.t

  type forwardOutFunction = AdjGraph.EDFT.t -> packet -> packet

  type forwardInFunction = AdjGraph.EDFT.t -> packet -> packet

  type switchInitFunction = AdjGraph.Vertex.t -> packet

  type nodeHistoryInitFunction = AdjGraph.Vertex.t -> hV

  type edgeHistoryInitFunction = AdjGraph.Vertex.t -> hE

  type nodeHistoryLogFunction = AdjGraph.Vertex.t -> packet -> hV -> hV

  type edgeHistoryLogFunction = AdjGraph.EDFT.t -> packet -> hE -> hE

  type dataplane = {
    switches : switchState;
    nodeHistory : historyV;
    edgeHistory : historyE;
    worklist : AdjGraph.Vertex.t list;
  }

  type forwardSolutions = unit Solution.forwardSolutions

  (* For profiling *)
  let fwd_time = ref 0.0

  let logging_time = ref 0.0

  (* For debugging purposes *)
  let printEdgeHistory v e =
    let leaves = Mtbddc.leaves (Obj.magic v) in
    Printf.printf "History for edge : %s\n" (AdjGraph.Edge.to_string e);
    Array.iter (fun v -> Printf.printf "%d, " v) leaves;
    Printf.printf "\n\n"

  (* For debugging purposes *)
  let printState s =
    Printf.printf "switch state:\n";
    AdjGraph.VertexMap.iter
      (fun i ps ->
        Printf.printf "%d : %s\n" i
          (Collections.printList (fun _ -> "p") ps "[" ";" "]"))
      s.switches;
    Printf.printf "worklist:\n%s"
      (Collections.printList
         (fun i -> string_of_int i)
         s.worklist "[" ";" "]\n");
    AdjGraph.EdgeMap.iter (fun e vs -> printEdgeHistory vs e) s.edgeHistory

  (* [create_state n initSwitch hinitV hinitE] where n is the number of nodes,
      initSwitch is the init function for switches and hinitV/hinitE the initial histories *)
  let create_state (g : AdjGraph.t) initSwitch hinitV hinitE bot : dataplane =
    let switches, nodeHistory, worklist =
      AdjGraph.fold_vertex
        (fun n (accSt, accH, wklist) ->
          let p = initSwitch n in
          let accSt, wklist =
            if p = bot then (AdjGraph.VertexMap.add n [] accSt, wklist)
            else (AdjGraph.VertexMap.add n [ p ] accSt, n :: wklist)
          in
          (accSt, AdjGraph.VertexMap.add n (hinitV n) accH, wklist))
        g
        (AdjGraph.VertexMap.empty, AdjGraph.VertexMap.empty, [])
    in
    let edgeHistory =
      AdjGraph.fold_edges_e
        (fun e accH ->
          AdjGraph.EdgeMap.add e (hinitE (AdjGraph.Edge.label e)) accH)
        g AdjGraph.EdgeMap.empty
    in
    let s = { switches; nodeHistory; edgeHistory; worklist } in
    (* printState s; *)
    s

  let simulate_forward_step (fwdIn : forwardInFunction)
      (fwdOut : forwardOutFunction) (logV : nodeHistoryLogFunction)
      (logE : edgeHistoryLogFunction) (bot : packet) (s : dataplane) =
    let packetDropped packet = packet = bot in
    let process_packet packet origin neighbor s =
      let edge = AdjGraph.find_edge G.graph origin neighbor in
      let edge_id = AdjGraph.E.label edge in

      (* printEdgeHistory (AdjGraph.EdgeMap.find edge s.edgeHistory) edge; *)
      (* the packet after applying the outgoing policy/filters *)
      let packetOut = fwdOut edge_id packet in

      (* add the outgoing packet that traversed the edge to the history of the
         edge (origin,neighbor) *)
      let historyEdge' =
        logE edge_id packetOut (AdjGraph.EdgeMap.find edge s.edgeHistory)
      in
      (* Printf.printf "history after packetOut\n";
         printEdgeHistory historyEdge' edge; *)
      if packetDropped packetOut then
        {
          (* If the packet was dropped, only the edge history changes *)
          s with
          edgeHistory = AdjGraph.EdgeMap.add edge historyEdge' s.edgeHistory;
        }
      else
        let packetIn = fwdIn edge_id packetOut in
        let historyNode' =
          logV neighbor packetIn
            (AdjGraph.VertexMap.find neighbor s.nodeHistory)
        in
        if packetDropped packetIn then
          {
            s with
            edgeHistory = AdjGraph.EdgeMap.add edge historyEdge' s.edgeHistory;
            nodeHistory =
              AdjGraph.VertexMap.add neighbor historyNode' s.nodeHistory;
          }
        else
          let switchSt =
            AdjGraph.VertexMap.find_default [] neighbor s.switches
          in
          let switches', worklist' =
            if switchSt = [] then
              ( AdjGraph.VertexMap.add neighbor [ packetIn ] s.switches,
                neighbor :: s.worklist )
            else
              ( AdjGraph.VertexMap.add neighbor (packetIn :: switchSt) s.switches,
                s.worklist )
          in
          {
            switches = switches';
            edgeHistory = AdjGraph.EdgeMap.add edge historyEdge' s.edgeHistory;
            nodeHistory =
              AdjGraph.VertexMap.add neighbor historyNode' s.nodeHistory;
            worklist = worklist';
          }
    in
    let origin, worklist' = (List.hd s.worklist, List.tl s.worklist) in
    (* Printf.printf "working on switch: %d with state: \n" origin;
       printState s; *)
    let packets, switches' = AdjGraph.VertexMap.extract origin s.switches in
    let s = { s with worklist = worklist'; switches = switches' } in
    let neighbors = AdjGraph.succ G.graph origin in
    let s' =
      BatList.fold_left
        (fun s v ->
          List.fold_left
            (fun s packet -> process_packet packet origin v s)
            s packets)
        s neighbors
    in
    (* Printf.printf "Resulted in state:\n";
       printState s'; *)
    s'

  let rec simulate_forward_init fwdIn fwdOut logV logE bot (s : dataplane) =
    match s.worklist with
    | [] -> (s.nodeHistory, s.edgeHistory)
    | _ ->
        let s' = simulate_forward_step fwdIn fwdOut logV logE bot s in
        simulate_forward_init fwdIn fwdOut logV logE bot s'

  let forwarding_solutions = ref []

  (* Start the forwarding process *)
  let simulate_forwarding record_fns hvName heName hv_ty_id he_ty_id
      (initSwitch : switchInitFunction) (fwdOut : forwardOutFunction)
      (fwdIn : forwardInFunction) hinitV hinitE logV logE bot =
    let s = create_state G.graph initSwitch hinitV hinitE bot in
    let fwdOut e x =
      Profile.time_profile_total fwd_time (fun () -> fwdOut e x)
    in
    let fwdIn e x = Profile.time_profile_total fwd_time (fun () -> fwdIn e x) in
    let logV u p hv =
      Profile.time_profile_total logging_time (fun () -> logV u p hv)
    in
    let logE e p he =
      Profile.time_profile_total logging_time (fun () -> logE e p he)
    in
    let hv, he = simulate_forward_init fwdIn fwdOut logV logE bot s in

    Printf.printf "Forwarding time: %f\n" !fwd_time;
    Printf.printf "Logging time: %f\n" !logging_time;
    let _, defaultV = AdjGraph.VertexMap.choose hv in
    let _, defaultE = AdjGraph.EdgeMap.choose he in
    (* Constructing a function from the solutions *)
    let bdd_base_V =
      BddMap.create
        ~key_ty_id:
          (Collections.TypeIds.get_id CompileBDDs.type_store
             Syntax.(concrete TNode))
        ~val_ty_id:hv_ty_id defaultV
    in
    let bdd_base_E =
      BddMap.create
        ~key_ty_id:
          (Collections.TypeIds.get_id CompileBDDs.type_store
             Syntax.(concrete TEdge))
        ~val_ty_id:he_ty_id defaultE
    in
    let bdd_full_V =
      AdjGraph.VertexMap.fold
        (fun n v acc ->
          BddMap.update (Obj.magic record_fns) acc (Obj.magic n) (Obj.magic v))
        hv bdd_base_V
    in
    let bdd_full_E =
      AdjGraph.EdgeMap.fold
        (fun e v acc ->
          BddMap.update (Obj.magic record_fns) acc
            (Obj.magic (AdjGraph.Edge.label e))
            (Obj.magic v))
        he bdd_base_E
    in

    (* storing the histories for printing *)
    (let open Solution in
    forwarding_solutions :=
      {
        hvName;
        heName;
        historyV_ty =
          Collections.TypeIds.get_elt CompileBDDs.type_store hv_ty_id;
        historyE_ty =
          Collections.TypeIds.get_elt CompileBDDs.type_store he_ty_id;
        historyV = hv;
        historyE = he;
      }
      :: !forwarding_solutions);

    (bdd_full_V, bdd_full_E)
end

(* SRP simulation statistics *)

module RouteComputationStats = struct
  let transfer_time = ref 0.0

  let merge_time = ref 0.0

  let merges = ref 0

  let incr_merges = ref 0

  let transfers = ref 0

  type simulationStats = {
    transTime : float;
    mergeTime : float;
    mergeNumber : int;
    incrMergeNumber : int;
    transferNumber : int;
  }

  let perSimulationStats : simulationStats PrimitiveCollections.StringMap.t ref
      =
    ref StringMap.empty

  let clearSimulationStats () =
    incr_merges := 0;
    merges := 0;
    transfers := 0;
    transfer_time := 0.0;
    merge_time := 0.0

  let logSimulationStats name =
    perSimulationStats :=
      StringMap.add name
        {
          transTime = !transfer_time;
          mergeTime = !merge_time;
          transferNumber = !transfers;
          mergeNumber = !merges;
          incrMergeNumber = !incr_merges;
        }
        !perSimulationStats;
    clearSimulationStats ()

  let printSimulationStats name stats =
    Printf.printf
      "Route computation Stats for %s\n---------------------------\n" name;
    Printf.printf "Number of incremental merges: %d\n" stats.incrMergeNumber;
    Printf.printf "Number of calls to merge: %d\n" stats.mergeNumber;
    Printf.printf "Number of transfers: %d\n" stats.transferNumber;
    Printf.printf "Transfer time: %f\n" stats.transTime;
    Printf.printf "Merge time: %f\n" stats.mergeTime

  let printTotalSimulationStats () =
    let total =
      StringMap.fold
        (fun _ v acc ->
          {
            transTime = v.transTime +. acc.transTime;
            mergeTime = v.mergeTime +. acc.mergeTime;
            transferNumber = v.transferNumber + acc.transferNumber;
            mergeNumber = v.mergeNumber + acc.mergeNumber;
            incrMergeNumber = v.incrMergeNumber + acc.incrMergeNumber;
          })
        !perSimulationStats
        {
          transTime = 0.0;
          mergeTime = 0.0;
          transferNumber = 0;
          mergeNumber = 0;
          incrMergeNumber = 0;
        }
    in
    printSimulationStats "all simulations" total
end

module SrpSimulation (G : Topology) : SrpSimulationSig = struct
  (* Simulation States *)
  (* Solution Invariant: All valid graph vertices are associated with an
     attribute initially (and always) *)
  type 'a solution = 'a AdjGraph.VertexMap.t

  let graph = G.graph

  (* The extended solution of a node includes the route selected + the messages received from each neighbor*)
  type 'a extendedSolution = ('a solution * 'a) AdjGraph.VertexMap.t

  type queue = AdjGraph.Vertex.t QueueSet.queue

  type 'a state = 'a extendedSolution * queue

  let create_state (n : int) init : 'a state =
    let rec loop n (q : queue) m =
      if Pervasives.compare n 0 > 0 then
        let next_n = n - 1 in
        let next_q = QueueSet.add q next_n in
        let init_n = init next_n in
        let next_m =
          AdjGraph.VertexMap.add next_n
            (AdjGraph.VertexMap.singleton next_n init_n, init_n)
            m
        in
        loop next_n next_q next_m
      else (m, q)
    in
    let s =
      loop n (QueueSet.empty Pervasives.compare) AdjGraph.VertexMap.empty
    in
    s

  exception Require_false

  let get_attribute (v : AdjGraph.VertexMap.key) (s : 'a extendedSolution) =
    match AdjGraph.VertexMap.Exceptionless.find v s with
    | None -> failwith ("no attribute at vertex " ^ string_of_int v)
    | Some a -> a

  let attr_equal = ref (fun _ _ -> true)

  let simulate_step trans merge (s : 'a extendedSolution) (origin : int) =
    let do_neighbor (_, initial_attribute) (s, todo) neighbor =
      let edge_id =
        AdjGraph.E.label @@ AdjGraph.find_edge graph origin neighbor
      in
      (* Compute the incoming attribute from origin *)
      let n_incoming_attribute = trans edge_id initial_attribute in
      let n_received, n_old_attribute = get_attribute neighbor s in
      match AdjGraph.VertexMap.Exceptionless.find origin n_received with
      | None ->
          (* If this is the first message from this node then add it to the received messages of n*)
          let new_entry =
            AdjGraph.VertexMap.add origin n_incoming_attribute n_received
          in
          (*compute new merge and decide whether best route changed and it needs to be propagated*)
          let n_new_attribute =
            merge neighbor n_old_attribute n_incoming_attribute
          in
          if
            Mtbddc.is_equal
              (Obj.magic n_old_attribute)
              (Obj.magic n_new_attribute)
          then
            ( AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s,
              todo )
          else
            ( AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s,
              neighbor :: todo )
      | Some old_attribute_from_x ->
          (* if n had already received a message from origin then we may need to recompute everything*)
          (* Withdraw route received from origin *)
          let n_received = AdjGraph.VertexMap.remove origin n_received in
          (* Merge the old route from with the new route from origin *)
          let compare_routes =
            merge neighbor old_attribute_from_x n_incoming_attribute
          in
          (* This is a hack because merge may not be selective *)
          let dummy_new =
            (* n_incoming_attribute *)
            merge neighbor n_incoming_attribute n_incoming_attribute
          in
          (*if the merge between new and old route from origin is equal to the new route from origin*)
          if Mtbddc.is_equal (Obj.magic compare_routes) (Obj.magic dummy_new)
          then
            (* incr incr_merges; *)
            (*we can incrementally compute in this case*)
            let n_new_attribute =
              merge neighbor n_old_attribute n_incoming_attribute
            in
            let new_entry =
              AdjGraph.VertexMap.add origin n_incoming_attribute n_received
            in
            (*update the todo list if the node's solution changed.*)
            if
              Mtbddc.is_equal
                (Obj.magic n_old_attribute)
                (Obj.magic n_new_attribute)
            then
              ( AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s,
                todo )
            else
              ( AdjGraph.VertexMap.add neighbor (new_entry, n_new_attribute) s,
                neighbor :: todo )
          else
            (* In this case, we need to do a full merge of all received routes *)
            let best =
              AdjGraph.VertexMap.fold
                (fun _ v acc -> merge neighbor v acc)
                n_received n_incoming_attribute
            in
            let newTodo =
              if Mtbddc.is_equal (Obj.magic n_old_attribute) (Obj.magic best)
              then todo
              else neighbor :: todo
            in
            (*add the new received route for n from origin*)
            let n_received =
              AdjGraph.VertexMap.add origin n_incoming_attribute n_received
            in
            (AdjGraph.VertexMap.add neighbor (n_received, best) s, newTodo)
    in
    let initial_attribute = get_attribute origin s in
    let neighbors = AdjGraph.succ G.graph origin in
    BatList.fold_left (do_neighbor initial_attribute) (s, []) neighbors

  (* simulate_init s q simulates srp starting with initial state (s,q) *)
  let rec simulate_init trans merge ((s, q) : 'a state) =
    match QueueSet.pop q with
    | None -> s
    | Some (next, rest) ->
        (* (if (Cudd.Man.get_node_count BddUtils.mgr > 1000000) then
           BddUtils.set_reordering (Cmdline.get_cfg ()).reordering); *)
        let s', more = simulate_step trans merge s next in
        simulate_init trans merge (s', QueueSet.add_all rest more)

  (* simulate for at most k steps *)
  let simulate_init_bound trans merge ((s, q) : 'a state) k =
    let rec loop s q k =
      if k <= 0 then (s, q)
      else
        match QueueSet.pop q with
        | None -> (s, q)
        | Some (next, rest) ->
            let s', more = simulate_step trans merge s next in
            loop s' (QueueSet.add_all rest more) (k - 1)
    in
    loop s q k

  (* List holding the solutions of solved SRPs*)
  let solved : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list ref =
    ref []

  let simulate_solve record_fns attr_ty_id name init trans merge =
    let mgr = BddUtils.mgr in
    Cudd.Man.group mgr 0 !BddMap.svars Cudd.Man.MTR_DEFAULT;
    let s = create_state (AdjGraph.nb_vertex G.graph) init in
    let trans e x =
      incr RouteComputationStats.transfers;
      Profile.time_profile_total RouteComputationStats.transfer_time (fun () ->
          trans e x)
    in
    let merge u x y =
      incr RouteComputationStats.merges;
      Profile.time_profile_total RouteComputationStats.merge_time (fun () ->
          merge u x y)
    in
    let vals =
      match (Cmdline.get_cfg ()).bound with
      | None ->
          simulate_init trans merge s
          |> AdjGraph.VertexMap.map (fun (_, v) -> v)
      | Some b ->
          fst @@ simulate_init_bound trans merge s b
          |> AdjGraph.VertexMap.map (fun (_, v) -> v)
    in

    RouteComputationStats.logSimulationStats name;

    let default = AdjGraph.VertexMap.choose vals |> snd in
    (* Constructing a function from the solutions *)
    let bdd_base =
      BddMap.create
        ~key_ty_id:
          (Collections.TypeIds.get_id CompileBDDs.type_store
             Syntax.(concrete TNode))
        ~val_ty_id:attr_ty_id default
    in
    let bdd_full =
      AdjGraph.VertexMap.fold
        (fun n v acc ->
          BddMap.update (Obj.magic record_fns) acc (Obj.magic n) (Obj.magic v))
        vals bdd_base
    in

    (* Storing the AdjGraph.VertexMap in the solved list, but returning
       the function to the ProbNV program *)
    solved :=
      ( name,
        ( Obj.magic vals,
          Collections.TypeIds.get_elt CompileBDDs.type_store attr_ty_id ) )
      :: !solved;
    bdd_full

  let assertions : (string * bool Mtbddc.t * BddFunc.t option) list ref = ref []

  module Forwarding = ForwardingSimulation (G)
  include Forwarding

  let simulate_forwarding = Forwarding.simulate_forwarding
end

module SrpLazySimulation (G : Topology) : SrpSimulationSig = struct
  (* Simulation States *)
  (* Solution Invariant: All valid graph vertices are associated with an
     attribute initially (and always) *)

  let graph = G.graph

  type 'a nodeState = { labels : 'a; received : 'a AdjGraph.VertexMap.t }

  type globalState = {
    mutable queue : AdjGraph.Vertex.t BatQueue.t;
    mutable queueSet : AdjGraph.VertexSet.t;
    mutable worklist : AdjGraph.VertexSet.t array;
  }

  type 'a state = 'a nodeState AdjGraph.VertexMap.t * globalState

  let create_initial_state (n : int) initArr : 'a state =
    let q = BatQueue.create () in

    (* Add to the initial queue only the nodes that have some initial route *)
    let qMap =
      BatArray.fold_lefti
        (fun acc i route ->
          BatMap.update_stdlib route
            (fun is ->
              match is with None -> Some [ i ] | Some is -> Some (i :: is))
            acc)
        BatMap.empty initArr
    in
    let _, maxElts = BatMap.max_binding qMap in
    let qSet =
      List.fold_left
        (fun acc i ->
          BatQueue.add i q;
          AdjGraph.VertexSet.add i acc)
        AdjGraph.VertexSet.empty maxElts
    in

    let initGlobal =
      {
        queue = q;
        queueSet = qSet;
        worklist = Array.init n (fun i -> AdjGraph.VertexSet.singleton i);
      }
    in
    (AdjGraph.VertexMap.empty, initGlobal)

  (* let get_attribute (v : AdjGraph.VertexMap.key) (local: 'a nodeState AdjGraph.VertexMap.t) =
     match AdjGraph.VertexMap.Exceptionless.find v local).labels *)

  let get_attribute_exn (v : AdjGraph.VertexMap.key)
      (local : 'a nodeState AdjGraph.VertexMap.t) =
    (AdjGraph.VertexMap.find v local).labels

  let get_local_state (v : AdjGraph.VertexMap.key)
      (local : 'a nodeState AdjGraph.VertexMap.t) =
    AdjGraph.VertexMap.Exceptionless.find v local

  let attr_equal = ref (fun _ _ -> true)

  let updateNeighbors u global =
    let neighbors = AdjGraph.succ G.graph u in
    BatList.iter
      (fun v ->
        if not (AdjGraph.VertexSet.mem v global.queueSet) then
          BatQueueExt.add v global.queue;
        global.queueSet <- AdjGraph.VertexSet.add v global.queueSet;
        global.worklist.(v) <- AdjGraph.VertexSet.add u global.worklist.(v))
      neighbors

  (* Performs the sending of message from every node [v] in [todoSet] to [u].*)
  let simulate_step init trans merge local global u todoSet =
    let do_neighbor change_bit v local =
      (* Processing message from v to u *)
      (* Printf.printf "Processing message from: %d to %d\n" v u; *)

      (* Compute the incoming attribute from v *)
      (* init u can only be computed once so this is ok *)
      let n_incoming_attribute =
        if u = v then init.(u)
        else
          (* Printf.printf "  Size of message from %d: %d\n" v
               (Cudd.Mtbddc.size (Obj.magic (get_attribute_exn v local)));
             printBdd (Obj.magic (get_attribute_exn v local)); *)
          let edge_id = AdjGraph.E.label @@ AdjGraph.find_edge graph v u in
          trans edge_id (get_attribute_exn v local)
      in

      match AdjGraph.VertexMap.Exceptionless.find u local with
      | None ->
          (* If we haven't processed node u before *)
          (* Create an inbox for u, with a message from v *)
          let inbox_u = AdjGraph.VertexMap.singleton v n_incoming_attribute in
          (* Create a label for u *)
          let local' =
            AdjGraph.VertexMap.add u
              { labels = n_incoming_attribute; received = inbox_u }
              local
          in
          (* The attribute changed, so log that to update u's neighbors *)
          (true, local')
      | Some { labels = labu; received = inbox_u } -> (
          (* If we have processed node u before *)

          (* Search the inbox of node u to see if we have processed node v before *)
          match
            try Some (AdjGraph.VertexMap.extract v inbox_u)
            with Not_found -> None
          with
          | None ->
              (* If this is the first message from this node then add it to the received messages of u*)
              let inbox_u' =
                AdjGraph.VertexMap.add v n_incoming_attribute inbox_u
              in
              (*compute the merge and decide whether best route changed and it needs to be propagated*)
              let n_new_attribute = merge u labu n_incoming_attribute in
              ( change_bit
                || not
                     (Mtbddc.is_equal (Obj.magic labu)
                        (Obj.magic n_new_attribute)),
                AdjGraph.VertexMap.add u
                  { labels = n_new_attribute; received = inbox_u' }
                  local )
          | Some (old_attribute_from_v, inbox_u') ->
              (* if u had already received a message from v then we may need to recompute everything*)
              (* Withdraw route received from v *)

              (* Merge the old route from v with the new route from v *)
              let compare_routes =
                merge u old_attribute_from_v n_incoming_attribute
              in
              (* This is a hack because merge may not be selective *)
              let dummy_new =
                (* n_incoming_attribute *)
                merge u n_incoming_attribute n_incoming_attribute
              in
              (*if the merge between new and old route from origin is equal to the new route from v*)
              if
                Mtbddc.is_equal (Obj.magic compare_routes) (Obj.magic dummy_new)
              then (
                incr RouteComputationStats.incr_merges;
                (*we can incrementally compute in this case*)
                let u_new_attribute = merge u labu n_incoming_attribute in
                (* add the new message from v to u's inbox *)
                let inbox_u' =
                  AdjGraph.VertexMap.add v n_incoming_attribute inbox_u'
                in
                (*update the todo bit if the node's solution changed.*)
                ( change_bit
                  || not
                       (Mtbddc.is_equal (Obj.magic labu)
                          (Obj.magic u_new_attribute)),
                  AdjGraph.VertexMap.add u
                    { labels = u_new_attribute; received = inbox_u' }
                    local ) )
              else
                (* In this case, we need to do a full merge of all received routes *)
                (*TODO: maybe this isn't the most efficient way to implement this, we should do the full merge once
                      we have processed all incoming messages *)
                let u_new_attribute =
                  AdjGraph.VertexMap.fold
                    (fun _ route acc -> merge u route acc)
                    inbox_u' n_incoming_attribute
                in
                (* add the new message from v to u's inbox *)
                let inbox_u' =
                  AdjGraph.VertexMap.add v n_incoming_attribute inbox_u'
                in
                ( change_bit
                  || not
                       (Mtbddc.is_equal (Obj.magic labu)
                          (Obj.magic u_new_attribute)),
                  AdjGraph.VertexMap.add u
                    { labels = u_new_attribute; received = inbox_u' }
                    local ) )
    in
    (* Printf.printf "Processing node: %d\n" u; *)
    let change, local' =
      AdjGraph.VertexSet.fold
        (fun v (changed, local) ->
          let change_bit, local' = do_neighbor changed v local in
          (change_bit || changed, local'))
        todoSet (false, local)
    in
    (* empty the worklist for u, it should have been fully processed *)
    global.worklist.(u) <- AdjGraph.VertexSet.empty;

    (* Remove next from the queue schedule and the queueset *)
    BatQueueExt.filter_first (fun i -> i = u) global.queue;
    global.queueSet <- AdjGraph.VertexSet.remove u global.queueSet;

    (* BatQueue.pop global.queue; *)

    (* Printf.printf "Queue after removing next";
       BatQueue.iter (fun i -> Printf.printf "%d," i) global.queue;
       Printf.printf "\n"; *)

    (* If the label of u has changed then signal its neighbors, i.e. add them to
       the queue and to the worklist with a dependency from u*)
    if change then (
      updateNeighbors u global;
      local' )
    else local'

  (* returns the first element not satisfying pred in the set s. Returns None if no
     such element exists. *)
  let rec findMin pred (s : AdjGraph.VertexSet.t) : AdjGraph.Vertex.t option =
    match try Some (AdjGraph.VertexSet.pop s) with Not_found -> None with
    | None -> None
    | Some (x, s) -> if pred x then findMin pred s else Some x

  let rec findMinLargest u wklist (s : AdjGraph.VertexSet.t) : AdjGraph.Vertex.t
      =
    let x, _ =
      AdjGraph.VertexSet.fold
        (fun x (accx, accsz) ->
          let sz = AdjGraph.VertexSet.cardinal wklist.(x) in
          if x <> u && sz > accsz then (x, sz) else (accx, accsz))
        s (u, 0)
    in
    x

  let skips = ref 0

  (* Process a node in the schedule *)
  let rec processNode next init trans merge local global i =
    (* Check the worklist for the nodes next should read messages from *)
    let wklist = global.worklist in
    let todoSet = wklist.(next) in

    (* Check that the node only depends on nodes that are not in the schedule
           (with the exception of the node itself) *)
    let pred v = v = next || wklist.(v) = AdjGraph.VertexSet.empty in
    (* how many steps to skip, i = 1 allows 1 skip *)
    if i = !skips then simulate_step init trans merge local global next todoSet
    else
      (* let x = findMinLargest next wklist todoSet in
         if x = next then simulate_step init trans merge local global next todoSet
         else processNode x init trans merge local global (i + 1) *)
      match findMin pred todoSet with
      | None ->
          (* If all elements satisfy pred, i.e. they have no outstanding deps, continue processing next *)
          simulate_step init trans merge local global next todoSet
      | Some x ->
          (* If next depends on x and x needs to be processed too, then skip
              the queue and process x *)
          processNode x init trans merge local global (i + 1)

  (* simulate_init s q simulates srp starting with initial state (s,q) *)
  let rec simulate_init init trans merge global local =
    match BatQueue.Exceptionless.peek global.queue with
    (* match BatQueue.take_opt global.queue with *)
    | None -> local
    | Some next ->
        (* Printf.printf "Queue top: %d," next; *)
        simulate_init init trans merge global
          (processNode next init trans merge local global 0)

  (* List holding the solutions of solved SRPs*)
  let solved : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list ref =
    ref []

  let simulate_solve record_fns attr_ty_id name init trans merge =
    let mgr = BddUtils.mgr in
    Cudd.Man.group mgr 0 !BddMap.svars Cudd.Man.MTR_DEFAULT;
    let n = AdjGraph.nb_vertex G.graph in
    let initArr = Array.init n (fun i -> init i) in
    let local, global = create_initial_state n initArr in
    let trans e x =
      incr RouteComputationStats.transfers;
      Profile.time_profile_total RouteComputationStats.transfer_time (fun () ->
          trans e x)
    in
    let merge u x y =
      incr RouteComputationStats.merges;
      Profile.time_profile_total RouteComputationStats.merge_time (fun () ->
          merge u x y)
    in
    skips := (Cmdline.get_cfg ()).sim_skip;
    let vals =
      simulate_init initArr trans merge global local
      |> AdjGraph.VertexMap.map (fun v -> v.labels)
    in
    RouteComputationStats.logSimulationStats name;

    let default = AdjGraph.VertexMap.choose vals |> snd in
    (* Constructing a function from the solutions *)
    let bdd_base =
      BddMap.create
        ~key_ty_id:
          (Collections.TypeIds.get_id CompileBDDs.type_store
             Syntax.(concrete TNode))
        ~val_ty_id:attr_ty_id default
    in
    let bdd_full =
      AdjGraph.VertexMap.fold
        (fun n v acc ->
          BddMap.update (Obj.magic record_fns) acc (Obj.magic n) (Obj.magic v))
        vals bdd_base
    in

    (* Storing the AdjGraph.VertexMap in the solved list, but returning
       the total map to the ProbNV program *)
    solved :=
      ( name,
        ( Obj.magic vals,
          Collections.TypeIds.get_elt CompileBDDs.type_store attr_ty_id ) )
      :: !solved;
    bdd_full

  let assertions : (string * bool Mtbddc.t * BddFunc.t option) list ref = ref []

  module Forwarding = ForwardingSimulation (G)
  include Forwarding

  let simulate_forwarding = Forwarding.simulate_forwarding
end

(* Given the attribute type of the network constructs an OCaml function
      that takes as input an OCaml value and creates a similar NV value.*)
let ocaml_to_nv_value record_fns (attr_ty : Syntax.ty) v : Syntax.value =
  match Syntax.get_mode attr_ty with
  | Some Concrete -> Embeddings.embed_value record_fns attr_ty v
  | Some Multivalue -> Embeddings.embed_multivalue record_fns attr_ty v
  | Some Symbolic -> failwith "Solution cannot be symbolic"
  | None -> failwith "No mode found"

let build_solution record_fns (vals, ty) =
  if (Cmdline.get_cfg ()).verbose then
    AdjGraph.VertexMap.map (fun v -> ocaml_to_nv_value record_fns ty v) vals
  else AdjGraph.VertexMap.empty

let build_forwarding record_fns fwd =
  let open Solution in
  if (Cmdline.get_cfg ()).verbose then
    {
      fwd with
      historyV =
        AdjGraph.VertexMap.map
          (fun v -> ocaml_to_nv_value record_fns fwd.historyV_ty v)
          fwd.historyV;
      historyE =
        AdjGraph.EdgeMap.map
          (fun e -> ocaml_to_nv_value record_fns fwd.historyE_ty e)
          fwd.historyE;
    }
  else
    {
      fwd with
      historyV = AdjGraph.VertexMap.empty;
      historyE = AdjGraph.EdgeMap.empty;
    }

(* Two modes of computation until we implement fast prob for all type of symbolics *)
let check_assertion
    ((name, a, cond) : string * bool Cudd.Mtbddc.t * BddFunc.t option)
    symbolic_bounds distrs =
  let cond =
    match cond with
    | Some (BBool b) -> Some b
    | None -> None
    | _ -> failwith "Impossible case - condition has typechecked to a boolean"
  in
  (* let prob' = BddUtils.computeTrueProbabilityOld *)
  let prob, counterExample =
    BddUtils.computeTrueProbability a symbolic_bounds distrs cond
  in
  (name, prob, counterExample)

let build_solutions nodes record_fns (fwd : unit Solution.forwardSolutions list)
    (sols : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list)
    (assertions : (string * bool Cudd.Mtbddc.t * BddFunc.t option) list) =
  let open Solution in
  let assertions = List.rev assertions in
  (* let arr = Array.init (Cudd.Man.get_bddvar_nb BddUtils.mgr) (fun i -> i) in
     Cudd.Man.shuffle_heap BddUtils.mgr arr; *)
  Cudd.Man.disable_autodyn BddUtils.mgr;

  let symbolic_bounds = List.rev !BddUtils.vars_list in
  let distrs = BddUtils.createDistributionMap symbolic_bounds in
  {
    assertions =
      Profile.time_profile "Time to check assertions" (fun () ->
          List.map
            (fun a ->
              (* TODO: generateSat when a counterexample is required *)
              check_assertion a symbolic_bounds distrs)
            assertions);
    solves =
      List.map
        (fun (name, sol) ->
          ( Var.create name,
            { sol_val = build_solution record_fns sol; attr_ty = snd sol } ))
        sols;
    forwarding = List.map (fun f -> build_forwarding record_fns f) fwd;
    nodes;
  }
