open ProbNv_lang.Syntax

val substitute : ProbNv_datastructures.Var.t -> exp -> exp -> exp

val inline_exp : exp ProbNv_datastructures.Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations
