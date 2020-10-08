type t = ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t

val store : ProbNv_datastructures.Var.t ProbNv_lang.Collections.ExpMap.t ref
val empty : unit -> 'a ProbNv_lang.Collections.VarMap.t

val fresh
  :  ProbNv_lang.Syntax.exp
  -> ProbNv_datastructures.Var.t * ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t

val union : ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t ->
ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t ->
ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t
val isEmpty : 'a ProbNv_lang.Collections.VarMap.t -> bool

val singleton
  :  ProbNv_datastructures.Var.t
  -> ProbNv_lang.Syntax.exp
  -> ProbNv_lang.Syntax.exp ProbNv_lang.Collections.VarMap.t

val fold
  :  (ProbNv_lang.Collections.VarMap.key -> 'a -> 'b -> 'b)
  -> 'a ProbNv_lang.Collections.VarMap.t
  -> 'b
  -> 'b
