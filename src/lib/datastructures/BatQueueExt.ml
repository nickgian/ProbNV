open Batteries
include BatQueue

type 'a cell = Nil | Cons of { content : 'a; mutable next : 'a cell }

type 'a t = {
  mutable length : int;
  mutable first : 'a cell;
  mutable last : 'a cell;
}

external of_abstr : 'a Queue.t -> 'a t = "%identity"

external to_abstr : 'a t -> 'a Queue.t = "%identity"

(* removes the first element of the queue that satisfies the given predicate *)
let filter_first f queue =
  let rec remove_next i prev =
    match i with
    | Nil -> () (* not found *)
    | Cons cell as cons ->
        if f cell.content then (
          match prev with
          | Nil ->
              (* If i is the first element of the queue *)
              if cell.next = Nil then queue.last <- Nil;
              queue.first <- cell.next;
              queue.length <- queue.length - 1
          | Cons pcell as pcons ->
              (* If i is not the first element, then previous should point to i.next
                 and i is now garbage *)
              if cell.next = Nil then queue.last <- pcons;
              pcell.next <- cell.next;
              queue.length <- queue.length - 1 )
        else remove_next cell.next cons
  in
  remove_next queue.first Nil

let filter_first f q = filter_first f (of_abstr q)

let add x q =
  let cell = Cons { content = x; next = Nil } in
  match q.last with
  | Nil ->
      q.length <- 1;
      q.first <- cell;
      q.last <- cell
  | Cons last ->
      q.length <- q.length + 1;
      last.next <- cell;
      q.last <- cell

let add x q = add x (of_abstr q)
