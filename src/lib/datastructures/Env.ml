open ProbNv_utils
module M = BatMap.Make (Var)

type 'a t = 'a M.t

let empty = M.empty

exception Unbound_var of string

let lookup env x =
  try M.find x env with Not_found -> raise (Unbound_var (Var.to_string x))

let lookup_opt env x = M.Exceptionless.find x env

let remove env x = M.remove x env

let update env x entry = M.add x entry env

(* update env1 with the bindings of env2.  If both environments have the same key, env2 shadows env1 *)
let updates env1 env2 = M.merge (fun _ v1 v2 -> match v2 with | None -> v1 | _ -> v2) env1 env2

let bind x entry = M.add x entry empty

let filter env f = M.filter f env

let map env f =
  M.map f env

let combineValues f env1 env2 =
  M.merge (fun _ v1 v2 -> Some (f (OCamlUtils.oget v1) (OCamlUtils.oget v2))) env1 env2

let to_string entry_to_string env =
  M.fold
    (fun k v s -> Var.to_string k ^ "=" ^ entry_to_string v ^ ";" ^ s)
    env ""

let to_list env = M.bindings env

let compare = M.compare

let equal = M.equal

let hash m = M.fold (fun x v acc -> (Hashtbl.hash x) + (Hashtbl.hash v) + acc) m 0
