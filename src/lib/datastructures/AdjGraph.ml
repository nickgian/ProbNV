open Graph
open ProbNv_utils.PrimitiveCollections

(*** Module definitions ***)

module Vertex = struct
  type t = int

  (* Really should be Syntax.node, but that causes a dependency loop *)

  let compare = Pervasives.compare

  let equal a b = compare a b = 0

  let hash = Hashtbl.hash

  let to_string = string_of_int
end

module EDFT : Graph.Sig.ORDERED_TYPE_DFT with type t = int = struct
  type t = int

  let default = 0

  let compare = compare
end

include Persistent.Digraph.ConcreteLabeled (Vertex) (EDFT)

module Edge = struct
  include E

  let equal a b = compare a b = 0

  let to_string e =
    Printf.sprintf "%s~%s" (Vertex.to_string (src e)) (Vertex.to_string (dst e))
end

module VertexMap = BetterMap.Make (Vertex)
module VertexSet = BetterSet.Make (Vertex)
module VertexSetSet = BetterSet.Make (VertexSet)
module VertexSetMap = BetterMap.Make (VertexSet)
module EdgeMap = BetterMap.Make (Edge)
module EdgeSet = BetterSet.Make (Edge)

(*** Printing ***)

let to_string g =
  Printf.sprintf "Vertices: {%s}\nEdges: {%s}"
    (fold_vertex (fun v acc -> acc ^ Vertex.to_string v ^ ";") g "")
    (fold_edges_e (fun e acc -> acc ^ Edge.to_string e ^ ";") g "")

(*** Vertex/Edge Utilities ***)

let fold_vertices (f : Vertex.t -> 'a -> 'a) (i : int) (acc : 'a) : 'a =
  let rec loop j = if i = j then acc else f j (loop (j + 1)) in
  loop 0

let vertices (g : t) = fold_vertex VertexSet.add g VertexSet.empty

let edges (g : t) = BatList.rev (fold_edges_e List.cons g [])

(*** Graph Creation **)

let create n edges =
  let g = fold_vertices (fun v g -> add_vertex g v) n empty in
  List.fold_left
    (fun g (u, v, i) ->
      let edge = E.create u i v in
      add_edge_e g edge)
    g edges
