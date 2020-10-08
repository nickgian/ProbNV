open ProbNv_lang.Syntax

val substitute : ProbNv_datastructures.Var.t -> exp -> exp -> exp

val inline_exp : (ty -> bool) -> exp ProbNv_datastructures.Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations

val inline_multivalue_declarations :
  declarations -> declarations