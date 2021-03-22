open Batteries
open ProbNv_lang
open Syntax
open ProbNv_utils
open RecordUtils
open Collections
open OCamlUtils
open ProbNv_solution
open ProbNv_compile

let ty_transformer _ ty = Some ty

let pattern_transformer _ _ _ = None

let value_transformer _ _ = None

let exp_transformer (recursors : Transformers.recursors) e =
  match e.e with
  | EMatch (e1, bs) -> (
      match e1.ety with
      | Some { typ = TEdge; mode = Some Concrete } ->
          Some
          (aexp(ematch (aexp
               ( eapp (evar @@ ProbNv_datastructures.Var.create "fromEdge") e1,
                 Some (concrete TEdge),
                 e1.espan)) (mapBranches (fun (p, ep) -> p, recursors.recurse_exp ep) bs), e.ety, e.espan))
      | _ -> None )
  | _ -> None

let map_back_transformer _ _ _ _ = None

let mask_transformer = map_back_transformer

(* Conveniently works in this case *)

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer)
    =
  toplevel_transformer ~name:"EdgeTransformer" ty_transformer
    pattern_transformer value_transformer exp_transformer map_back_transformer

let edge_transformer decls =
  make_toplevel Transformers.transform_declarations decls
