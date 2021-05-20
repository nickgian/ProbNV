open ProbNv_utils
(** Simulates an SRP compiled to a native OCaml progam *)

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

  val simulate_forwarding :
    (int * int -> 'a -> 'b) ->
    (* record_fns *)
    int ->
    (* vertex history type id *)
    int ->
    (* edge history type id *)
    string ->
    (* name of vertex variable *)
    string ->
    (* name of edge variable *)
    (int -> 'packet) ->
    (* fwdInit function *)
    (int -> 'packet -> 'packet) ->
    (*fwdOut function, int argument is the edge id *)
    (int -> 'packet -> 'packet) ->
    (*fwdOut function, int argument is the edge id *)
    (int -> 'historyV) ->
    (* hinitV function - int is the node id*)
    (int -> 'historyE) ->
    (* hinitE function - int is the edge id *)
    (int -> 'packet -> 'historyV -> 'historyV) ->
    (* logV function - int is the node id*)
    (int -> 'packet -> 'historyE -> 'historyE) ->
    (* logE function - int is the edge id*)
    'a CompileBDDs.t

  val graph : AdjGraph.t

  val solved : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list ref
  (** List of solutions, each entry is the name of the SRP, a map from nodes to solutions, and the type of routes *)

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

module ForwardingSimulation (G: Topology) =
struct
  (** Keeping track of the history of each node *)
  type 'hV historyV = 'hV AdjGraph.VertexMap.t
  (** Keeping track of the history of each link *)
  type 'hE historyE = 'hE AdjGraph.EdgeMap.t

  (** Current state of each switch/node *)
  type 'packet switchState = 'packet AdjGraph.VertexMap.t
  (** Current state of each interface/link *)
  type 'packet interfaceState = 'packet AdjGraph.EdgeMap.t 
  
    (* List holding the solutions of solved SRPs*)
    let solved : (string * (unit AdjGraph.VertexMap.t * Syntax.ty)) list ref =
      ref []
  
    let fwd_time = ref 0.0
  
    let logging_time = ref 0.0
  
    let simulate_forwarding record_fns hv_ty_id he_ty_id nameV nameE initFwd fwdIn fwdOut hinitV hinitE logV logE =
      let s = create_state (AdjGraph.nb_vertex G.graph) init in
      let trans e x =
        incr transfers;
        Profile.time_profile_total transfer_time (fun () -> trans e x)
      in
      let merge u x y =
        incr merges;
        Profile.time_profile_total merge_time (fun () -> merge u x y)
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
  
      Printf.printf "Number of incremental merges: %d\n" !incr_merges;
      Printf.printf "Number of calls to merge: %d\n" !merges;
      Printf.printf "Number of transfers: %d\n" !transfers;
      Printf.printf "Transfer time: %f\n" !transfer_time;
      Printf.printf "Merge time: %f\n" !merge_time;
      Printf.printf "Apply2 time: %f\n" !BddFunc.apply2_time;
      Printf.printf "Apply3 time: %f\n" !BddFunc.apply3_time;
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

  let merges = ref 0

  let incr_merges = ref 0

  let transfers = ref 0

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

  let transfer_time = ref 0.0

  let merge_time = ref 0.0

  let simulate_solve record_fns attr_ty_id name init trans merge =
    let mgr = BddUtils.mgr in
    Cudd.Man.group mgr 0 !BddMap.svars Cudd.Man.MTR_DEFAULT;
    let s = create_state (AdjGraph.nb_vertex G.graph) init in
    let trans e x =
      incr transfers;
      Profile.time_profile_total transfer_time (fun () -> trans e x)
    in
    let merge u x y =
      incr merges;
      Profile.time_profile_total merge_time (fun () -> merge u x y)
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

    Printf.printf "Number of incremental merges: %d\n" !incr_merges;
    Printf.printf "Number of calls to merge: %d\n" !merges;
    Printf.printf "Number of transfers: %d\n" !transfers;
    Printf.printf "Transfer time: %f\n" !transfer_time;
    Printf.printf "Merge time: %f\n" !merge_time;
    Printf.printf "Apply2 time: %f\n" !BddFunc.apply2_time;
    Printf.printf "Apply3 time: %f\n" !BddFunc.apply3_time;
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
            BatMap.update_stdlib route (fun is -> match is with | None -> Some [i] | Some is -> Some (i :: is)) acc)
        BatMap.empty initArr
    in
    let (_, maxElts) = BatMap.max_binding qMap in
    let qSet = List.fold_left (fun acc i -> BatQueue.add i q; AdjGraph.VertexSet.add i acc) AdjGraph.VertexSet.empty maxElts in

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

  let incr_merges = ref 0

  let merges = ref 0

  let transfers = ref 0

  let transfer_time = ref 0.0

  let merge_time = ref 0.0

  let updateNeighbors u global =
    let neighbors = AdjGraph.succ G.graph u in
    BatList.iter
      (fun v ->
        if not (AdjGraph.VertexSet.mem v global.queueSet) then
          BatQueueExt.add v global.queue;
        global.queueSet <- AdjGraph.VertexSet.add v global.queueSet;
        global.worklist.(v) <- AdjGraph.VertexSet.add u global.worklist.(v))
      neighbors

  let rec printBdd distr =
    match Mtbddc.inspect distr with
    | Leaf _ -> (
        match Obj.magic (Mtbddc.dval distr) with
        | None -> Printf.printf "Leaf: None\n"
        | Some v -> Printf.printf "Leaf: Some %d\n" v )
    | Ite (i, t, e) ->
        Printf.printf "top: %d: \n" i;
        Printf.printf "  dthen: ";
        printBdd t;
        Printf.printf "  delse: ";
        printBdd e

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
                incr incr_merges;
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
      incr transfers;
      Profile.time_profile_total transfer_time (fun () -> trans e x)
    in
    let merge u x y =
      incr merges;
      Profile.time_profile_total merge_time (fun () -> merge u x y)
    in
    skips := (Cmdline.get_cfg ()).sim_skip;
    let vals =
      simulate_init initArr trans merge global local
      |> AdjGraph.VertexMap.map (fun v -> v.labels)
    in
    Printf.printf "Number of incremental merges: %d\n" !incr_merges;
    Printf.printf "Number of calls to merge: %d\n" !merges;
    Printf.printf "Number of transfers: %d\n" !transfers;
    Printf.printf "Transfer time: %f\n" !transfer_time;
    Printf.printf "Merge time: %f\n" !merge_time;
    Printf.printf "Apply2 time: %f\n" !BddFunc.apply2_time;
    Printf.printf "Apply3 time: %f\n" !BddFunc.apply3_time;
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
end

(** Given the attribute type of the network constructs an OCaml function
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

(* Two modes of computation until we implement fast prob for all type of symbolics *)
let check_assertion
    ((name, a, cond) : string * bool Cudd.Mtbddc.t * BddFunc.t option) distrs =
  let cond =
    match cond with
    | Some (BBool b) -> Some b
    | None -> None
    | _ -> failwith "Impossible case - condition has typechecked to a boolean"
  in
  (* let prob' = BddUtils.computeTrueProbabilityOld *)
  let prob = BddUtils.computeTrueProbability a distrs cond in
  (name, prob)

let build_solutions nodes record_fns
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
              check_assertion a distrs)
            assertions);
    solves =
      List.map
        (fun (name, sol) ->
          ( Var.create name,
            { sol_val = build_solution record_fns sol; attr_ty = snd sol } ))
        sols;
    nodes;
  }
