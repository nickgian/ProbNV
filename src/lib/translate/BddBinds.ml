open ProbNv_lang
open ProbNv_datastructures
open Collections
open Syntax

(** * Datastructure used to bind free variables to a symbolic expression, i.e. ρ from the paper. *)

type t = exp VarMap.t

let store = ref ExpMap.empty

let empty () = VarMap.empty

let fresh (e : exp) : Var.t * exp VarMap.t =
  match ExpMap.Exceptionless.find e !store with
  | Some b -> (b, VarMap.empty)
  | None ->
      let b = Var.fresh "b" in
      store := ExpMap.add e b !store;
      (b, VarMap.add b e VarMap.empty)

let union rho1 rho2 =
  VarMap.fold
    (fun k v acc ->
      if VarMap.mem k acc then
        assert (Syntax.equal_exps ~cmp_meta:false (VarMap.find k acc) v);
      VarMap.add k v acc)
    rho1 rho2

let isEmpty rho1 = VarMap.is_empty rho1

let singleton (x : Var.t) (e : exp) : exp VarMap.t = VarMap.add x e VarMap.empty

let fold = VarMap.fold
