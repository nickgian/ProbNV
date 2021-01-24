open ProbNv_lang.Syntax
open ProbNv_solution

type recursors = {
  recurse_ty : ty -> ty;
  recurse_pattern : pattern -> ty -> pattern;
  recurse_value : value -> value;
  recurse_exp : exp -> exp;
}

type 'a transformer = recursors -> 'a -> 'a option

type pattern_transformer = recursors -> pattern -> ty -> pattern option

type map_back_transformer =
  (value -> ty -> value) -> Solution.t -> value -> ty -> value option

type 'a toplevel_transformer =
  name:string ->
  ty transformer ->
  pattern_transformer ->
  value transformer ->
  exp transformer ->
  map_back_transformer ->
  'a ->
  'a * Solution.map_back

val transform_declarations : declarations toplevel_transformer
