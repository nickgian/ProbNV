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

let toEdge_decl decls =
  let open ProbNv_datastructures in
  let n1_var = Var.create "n1" in
  let n2_var = Var.create "n2" in
  (* if compile then
       DLet
         (
           Var.create "toEdge",
           None,
           efun
             {arg = n1_var; argty = None; resty = None;
              body =
                efun
                  {arg = n2_var; argty = None; resty= None;
                   body = esome (e_val (vedge (n1_var, n2_var)))
                  }
             }
         )
     else*)
  (* print_endline @@ Nv_lang.Printing.declarations_to_string decls ; *)
  let edges = get_edges decls |> ProbNv_utils.OCamlUtils.oget in
  let default_branch =
    addBranch PWild
      (aexp
         ( e_val (voption None),
           Some (concrete @@ TOption (concrete TEdge)),
           Span.default ))
      emptyBranch
  in
  let branches =
    List.fold_left
      (fun bs (n1, n2) ->
        addBranch
          (PTuple [ PNode n1; PNode n2 ])
          (esome (e_val (vedge (n1, n2))))
          bs)
      default_branch edges
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
