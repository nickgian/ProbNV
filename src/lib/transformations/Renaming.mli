open ProbNv_lang
open ProbNv_solution

val alpha_convert_exp : ProbNv_datastructures.Var.t ProbNv_datastructures.Env.t -> Syntax.exp -> Syntax.exp

val alpha_convert_declarations :
     Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)