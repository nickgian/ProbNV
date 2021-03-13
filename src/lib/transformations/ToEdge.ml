open ProbNv_lang.Syntax

(***
   Simple implementation of the toEdge primitive in NV.
   toEdge is a function of type node -> node -> edge option, such that
   toEdge n1 n2 returns Some (n1~n2) if that edge exists in the graph, and
   None otherwise. This is used to ensure users cannot create invalid edge values.

   To avoid adding another primitive to the language grammar, we implement toEdge
   by automatically generating a function definition and adding it to the program.
   In essence, it is as if the user defined the function toEdge themselves at the
   beginning of each program, but we od it ourselves to ensure it's correct.

   For example, if the graph contains 3 edges 0~1, 1~0, and 1~2, we generate the
   following declaration:

   let toEdge n1 n2 =
   match n1, n2 with
   | 0n, 1n -> Some (0~1)
   | 1n, 0n -> Some (1~0)
   | 1n, 2n -> Some (1~2)
   | _ -> None
 ***)

let toEdge_decl topology =
  let open ProbNv_datastructures in
  let n1_var = Var.create "n1" in
  let n2_var = Var.create "n2" in
  let default_branch =
    addBranch PWild
      (aexp
         ( e_val (voption None),
           Some (concrete @@ TOption (concrete TEdge)),
           Span.default ))
      emptyBranch
  in
  let branches =
    AdjGraph.fold_edges_e
      (fun e bs ->
        addBranch
          (PTuple [ PNode (AdjGraph.E.src e); PNode (AdjGraph.E.dst e) ])
          (esome (e_val (vedge (AdjGraph.E.label e))))
          bs)
      topology default_branch
  in
  DLet
    ( Var.create "toEdge",
      efun
        {
          arg = n1_var;
          argty = Some (concrete TNode);
          resty =
            Some
              (concrete
                 (TArrow (concrete TNode, concrete @@ TOption (concrete TEdge))));
          fmode = Some Concrete;
          body =
            efun
              {
                arg = n2_var;
                argty = Some (concrete TNode);
                fmode = Some Concrete;
                resty = Some (concrete (TOption (concrete TEdge)));
                body = ematch (etuple [ evar n1_var; evar n2_var ]) branches;
              };
        } )

(* Likewise, a function returning the node points given an edge label - only for internal use! *)
let fromEdge_decl topology =
  let open ProbNv_datastructures in
  let e_var = Var.create "e" in
  let branches =
    AdjGraph.fold_edges_e
      (fun e bs ->
        addBranch
          (PEdgeId (AdjGraph.E.label e))
          (e_val
             (vtuple [ vnode @@ AdjGraph.E.src e; vnode @@ AdjGraph.E.dst e ]))
          bs)
      topology emptyBranch
  in
  DLet
    ( Var.create "fromEdge",
      efun
        {
          arg = e_var;
          argty = Some (concrete TEdge);
          resty = Some (concrete (TTuple [ concrete TNode; concrete TNode ]));
          fmode = Some Concrete;
          body = ematch (evar e_var) branches;
        } )
