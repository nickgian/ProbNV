open ProbNv_utils.PrimitiveCollections

module Vertex : sig
  type t = int

  (* Really should be Syntax.node, but that causes a dependency loop *)

  val to_string : t -> string

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int
end

module EDFT : Graph.Sig.ORDERED_TYPE_DFT with type t = int

(* graph *)
include module type of Graph.Persistent.Digraph.ConcreteLabeled (Vertex) (EDFT)

module Edge : sig
  include module type of E

  val equal : t -> t -> bool

  val to_string : t -> string
end

module VertexMap : BetterMap.S with type key = Vertex.t

module VertexSet : BetterSet.S with type elt = Vertex.t

module VertexSetSet : BetterSet.S with type elt = VertexSet.t

module VertexSetMap : BetterMap.S with type key = VertexSet.t

module EdgeSet : BetterSet.S with type elt = Edge.t

module EdgeMap : BetterMap.S with type key = Edge.t

val create : int -> (E.vertex * E.vertex) list -> t
(** Graph creation **)

(* Create graph with nodes and edges *)

val vertices : t -> VertexSet.t
(** Vertex/Edge retrieval **)

val edges : t -> Edge.t list

val fold_vertices : (Vertex.t -> 'a -> 'a) -> Vertex.t -> 'a -> 'a
(** fold over a set of vertices from 0 to n-1 *)

val to_string : t -> string
(** Printing *)
