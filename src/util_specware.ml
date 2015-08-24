(* Copyright (c) 2015, Kestrel Institute
All rights reserved.

This program is free software; you can redistribute it and/or modify it under
the terms of the included LICENSE.txt file.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the LICENSE.txt for more details. *)

open Names
open Loc
open Libnames
open Globnames
open Pp
open Errors
open Vernacexpr
open Vernacentries
open Constrexpr
open Constrexpr_ops
open Misctypes
open Decl_kinds
open Ppconstr
open Genredexpr
open Topconstr


(***
 *** Debugging support
 ***)

let debug_level = ref 1

let debug_printf level args =
  if !debug_level >= level then
    Format.eprintf args
  else
    Format.ifprintf Format.std_formatter args


(***
 *** Helper functions
 ***)

let dummy_loc = Loc.ghost

(* Map f on a list but only keep the "Some"s *)
let rec filter_map f l =
  match l with
  | [] -> []
  | x :: l' ->
     (match f x with
      | Some y -> y :: filter_map f l'
      | None -> filter_map f l')

(* Same as filter_map, but also reverse the list *)
let rev_filter_map f l =
  let rec helper l acc =
    match l with
    | [] -> acc
    | x :: l' ->
       helper l' (match f x with
                  | Some y -> (y::acc)
                  | None -> acc)
  in helper l []

(* Map f on a list and concatenate the results *)
let concat_map f l =
  List.concat (List.map f l)

(* Topo sort failed because of a circularity *)
exception TopoCircularity of int

(* Stable topological sort: sort l so that every element x comes after (or
   before, if reverse_p is set) its dependencies, favoring the existing ordering
   of l where possible. The dependencies of x are all nodes y whose key, given
   by the key function, is key_eq to a key in (deps x). *)
(* FIXME: use sets for deps instead of lists *)
let rec stable_topo_sort ?(reverse_p=false) loc key key_eq deps l =
  let arr = Array.of_list l in
  let arr_deps = Array.make (List.length l) [] in
  let visited = Array.make (List.length l) false in
  let rec get_node_by_key_help k j =
    if j >= Array.length arr then None
    else if key_eq k (key arr.(j)) then Some j
    else get_node_by_key_help k (j+1) in
  let get_node_by_key k = get_node_by_key_help k 0 in
  (* Perform a DFS to build the transitive closure of deps *)
  let rec build_node_deps path_to_i i =
    if visited.(i) then
      arr_deps.(i)
    else if List.mem i path_to_i then
      raise loc (TopoCircularity i)
    else
      let i_immed_deps = filter_map get_node_by_key (deps arr.(i)) in
      let i_deps = concat_map (build_node_deps (i::path_to_i)) i_immed_deps in
      visited.(i) <- true;
      arr_deps.(i) <- i_deps;
      i::i_deps
  in
  let _ = for i = 0 to Array.length arr_deps - 1 do
            ignore (build_node_deps [] i)
          done in
  let index_arr = Array.init (List.length l) (fun i -> i) in
  let _ = Array.stable_sort
            (fun i j ->
             if List.mem j arr_deps.(i) then
               (if reverse_p then 1 else -1)
             else if List.mem i arr_deps.(j) then
               (if reverse_p then -1 else 1)
             else j-i)
            index_arr in
  Array.to_list (Array.map (fun i -> arr.(i)) index_arr)


(***
 *** Helper functions for interacting with Coq
 ***)

(* Syntactic expressions for the sorts Type and Prop *)
let type_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GType [])
let prop_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GProp)

(* Pretty-print a term (a "construction") *)
let pp_constr fmt c = Pp.pp_with fmt (Printer.pr_constr c)

(* Pretty-print a glob_constr *)
let pp_glob_constr fmt c = Pp.pp_with fmt (Printer.pr_glob_constr c)

(* Pretty-print a term *)
let pp_constr_expr fmt c = Pp.pp_with fmt (Richpp.pr_constr_expr c)

(* Pretty-print a vernacular command *)
let pp_vernac fmt cmd = Pp.pp_with fmt (Ppvernac.Richpp.pr_vernac_body cmd)

(* Pretty-print a type error *)
let pp_type_error env fmt e =
  Pp.pp_with fmt (Himsg.explain_type_error env Evd.empty e)

(* Pretty-print a pretyping error *)
let pp_pretype_error env evd fmt e =
  Pp.pp_with fmt (Himsg.explain_pretype_error env evd e)

(* Pretty-print an auto_tactic *)
let pp_autotactic fmt tac = Pp.pp_with fmt (Hints.pr_autotactic tac)

(* Convert a term to a string *)
let constr_expr_to_string c = Pp.string_of_ppcmds (Richpp.pr_constr_expr c)

(* Accessors for located types *)
let located_elem (x : 'a located) = snd x
let located_loc (x : 'a located) = fst x

(* Build a name from an ident *)
let name_of_ident (id : Id.t) : Name.t = Name id

(* Build a located name from a located ident *)
let lname_of_lident (id : lident) : lname =
  (located_loc id, name_of_ident (located_elem id))

(* Test if an identifier has a given prefix, and if so, return the
   rest of the identifier after that prefix *)
let match_prefix id prefix =
  let pre_len = String.length prefix in
  let id_str = Id.to_string id in
  let id_len = String.length id_str in
  if id_len >= pre_len &&
       String.sub id_str 0 pre_len = prefix then
    Some (String.sub id_str pre_len (id_len - pre_len))
  else None

(* Check if an identifier has a given suffix *)
let has_suffix id suffix =
  let str = Id.to_string id in
  let str_len = String.length str in
  let suffix_len = String.length suffix in
  str_len > suffix_len &&
    suffix = String.sub str (str_len - suffix_len) suffix_len

(* Append a suffix to an Id, with "__" in between *)
let add_suffix id suffix =
  Id.of_string (Id.to_string id ^ "__" ^ suffix)

(* Append a suffix to an lident, with "__" in between *)
let add_suffix_l lid suffix =
  let (loc, id) = lid in
  (loc, add_suffix id suffix)

(* Build an expression for a variable from a located identifier *)
let mk_var lid = CRef (Ident lid, None)

(* Build a list of variable expressions *)
let mk_vars loc ids = List.map (fun id -> mk_var (loc, id)) ids

(* Build an anonymous hole term *)
let mk_hole loc =
  CHole (loc, None, IntroAnonymous, None)

(* Build a named hole term *)
let mk_named_hole loc id =
  CHole (loc, None, IntroIdentifier id, None)

(* Build a hole to be filled in by a tactic *)
let mk_tactic_hole loc tac =
  (CHole (loc, None, IntroAnonymous,
          Some (Genarg.in_gen (Genarg.rawwit Constrarg.wit_tactic) tac)))

(* Build a hole to be filled in by a specific, named tactic *)
let mk_named_tactic_hole loc tac_qualid =
  (CHole (loc, None, IntroAnonymous,
          Some (Genarg.in_gen
                  (Genarg.rawwit Constrarg.wit_tactic)
                  (Tacexpr.TacArg
                     (loc,
                      Tacexpr.TacCall
                        (loc, Qualid (loc, tac_qualid), []))))))

(* Build an application *)
let mk_app f args =
  CApp (dummy_loc, (None, f),
        List.map (fun arg -> (arg, None)) args)

(* Build an expression for a local reference applied to named implicit
   args, where the args are given as (name,value) pairs *)
let mk_ref_app_named_args loc r args =
  CApp (loc,
        (None, CRef (r, None)),
        List.map (fun (id,arg) ->
                  (arg, Some (dummy_loc, ExplByName id))) args)

(* Build an expression for a variable applied to named implicit args,
   where the args are given as (name,value) pairs *)
let mk_id_app_named_args loc id args =
  mk_ref_app_named_args loc (Ident (loc, id)) args

(* Build a qualified id (NOTE: dir is *not* reversed here) *)
let mk_qualid dir str =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) (Id.of_string str)

(* Cons an id onto the end of a qualid *)
let qualid_cons qualid id =
  let (mod_path,mod_name) = repr_qualid qualid in
  make_qualid (DirPath.make ([mod_name] @ DirPath.repr mod_path)) id

(* Build a term for a global constant, where dir lists the module path
   as a list (e.g., ["Coq"; "Init"; "Logic"]) and id is the id *)
let mk_reference dir name =
  CRef (Qualid (dummy_loc, mk_qualid dir name), None)

(* Get a string for a global reference *)
let global_to_string gr =
  match gr with
  | VarRef v -> raise dummy_loc (Failure "global_to_string")
  | ConstRef c -> Constant.to_string c
  | IndRef (i,_) -> MutInd.to_string i
  | ConstructRef _ -> raise dummy_loc (Failure "global_to_string")

(* Get the module for a global reference *)
let global_modpath gr =
  match gr with
  | VarRef _ -> raise dummy_loc (Failure "global_modpath")
  | ConstRef c -> Constant.modpath c
  | IndRef (i, _) -> MutInd.modpath i
  | ConstructRef ((i, _), _) -> MutInd.modpath i

(* Turn a global reference into a local one *)
let qualid_of_global gr =
  Nametab.shortest_qualid_of_global Id.Set.empty gr

(* Build an expression for a global applied to named implicit args *)
let mk_global_app_named_args gr args =
  mk_ref_app_named_args dummy_loc (Qualid (dummy_loc, qualid_of_global gr)) args

(* Build an exprssion for a global with @ in front of it *)
let mk_global_expl gr =
  CAppExpl (dummy_loc,
            (None, (Qualid (dummy_loc, qualid_of_global gr)), None),
            [])

(* Look up a defined constant by path list and string name *)
let mk_constant dir name =
  let qualid = mk_qualid dir name in
  match Nametab.locate qualid with
  | ConstRef c -> c
  | _ -> user_err_loc (dummy_loc, "_",
                       str ("Not a constant: " ^ string_of_qualid qualid))

(* Look up a constructor by a path list and a string name *)
let mk_constructor loc dir name =
  let qualid = mk_qualid dir name in
  match Nametab.locate qualid with
  | ConstructRef c -> c
  | _ -> user_err_loc (dummy_loc, "_",
                       str ("Not a constructor: " ^ string_of_qualid qualid))

(* Look up an identifier in the current module and make it fully qualified *)
let qualify_identifier id =
  let _ = debug_printf 2 "@[qualify_identifier: %s@]\n" (Id.to_string id) in
  qualid_of_global (Nametab.locate (qualid_of_ident id))

(* Make (the syntactic representation of) a single record field,
   filling in default (None) values for all the extra information such
   as notations, priority, etc. The coercion_p flag indicates whether
   to use a coercion field with ":>". *)
let mk_record_field (id, tp, coercion_p) =
  ((((if coercion_p then Some true else None),
     AssumExpr (lname_of_lident id, tp)), None), [])

(* Extract the name of a record field *)
let record_field_name fld =
  match fld with
  | (((_, AssumExpr (lid, _)), _), _) -> located_elem lid
  | _ -> raise dummy_loc (Failure "record_field_name")

(* Make an implicit {id:tp} assumption *)
let mk_implicit_assum id tp =
  LocalRawAssum ([(Loc.dummy_loc, Name id)], Default Implicit, tp)

(* Make an implicit {id} assumption *)
let mk_implicit_var_assum id =
  mk_implicit_assum id (CHole (dummy_loc,
                               Some (Evar_kinds.BinderType (Name id)),
                               IntroAnonymous, None))

(* Make an explicit (id:tp) assumption *)
let mk_explicit_assum id tp =
  LocalRawAssum ([(Loc.dummy_loc, Name id)], Default Explicit, tp)

(* Make an explicit variable assumption *)
let mk_explicit_var_assum id =
  mk_explicit_assum id (CHole (dummy_loc,
                               Some (Evar_kinds.BinderType (Name id)),
                               IntroAnonymous, None))

(* Add a definition to the current Coq image *)
let add_definition ?(hook = (fun _ _ -> ())) lid params type_opt body =
  let cmd = VernacDefinition
              ((None, Definition), lid,
               DefineBody (params, None, body, type_opt))
  in
  let _ = debug_printf 1 "@[add_definition command:@ %a@]\n" pp_vernac cmd in
  (* interp (located_loc id, cmd) *)
  Command.do_definition
    (located_elem lid) (Global, false, Definition) params None body type_opt
    (Lemmas.mk_hook hook)

(* Add a local definition, i.e., do a Let vernacular command *)
let add_local_definition id params type_opt body =
  let cmd = VernacDefinition
              ((Some Discharge, Definition), id,
               DefineBody (params, None, body, type_opt))
  in
  let _ = debug_printf 1 "@[add_local_definition command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc id, cmd)

(* Add an interactive definition, filled out by user tactics *)
let start_definition ?(hook = (fun _ _ -> ())) lid params tp =
  let cmd = VernacDefinition
              ((None, Definition), lid, ProveBody (params, tp))
  in
  let _ = debug_printf 1 "@[start_definition command:@ %a@]\n" pp_vernac cmd in
  (* interp (located_loc id, cmd) *)
  Lemmas.start_proof_com
    (Global, false, DefinitionBody Definition) [Some lid, (params, tp, None)]
    (Lemmas.mk_hook hook)

(* Start an interactively-proved theorem *)
let start_theorem ?(hook = (fun _ _ -> ())) thm_kind lid params tp =
  let cmd = VernacStartTheoremProof
              (thm_kind, [Some lid, (params, tp, None)], false)
  in
  let _ = debug_printf 1 "@[start_definition command:@ %a@]\n" pp_vernac cmd in
  (* interp (located_loc id, cmd) *)
  Lemmas.start_proof_com
    (Global, false, Proof thm_kind) [Some lid, (params, tp, None)]
    (Lemmas.mk_hook hook)

(* Add a definition using constrs, not constr_exprs *)
let add_definition_constr id type_opt (body, uctx) =
  let _ = debug_printf 1 "@[add_definition_constr: %s :=@ %a @]\n"
                       (Id.to_string id) pp_constr body in
  let def_entry =
    Declare.definition_entry ?types:type_opt
                             ~univs:(Evd.evar_context_universe_context uctx) body
  in
  Command.declare_definition
    id (Local, false, Definition) def_entry []
    (Lemmas.mk_hook (fun _ x -> x))


(* Add a type-class to the current Coq image, where is_op_class says
   whether to add an operational type-class in Type (if true) or a
   normal type-class in Prop (if false), and fields is a list of
   triples (id, type, coercion_p) to be passed to mk_record_field *)
let add_typeclass class_id is_op_class is_prop_class params fields =
  let cmd =
    VernacInductive (false, BiFinite,
                     [((false, class_id), params,
                       Some (if is_prop_class then prop_expr else type_expr),
                       Class is_op_class,
                       if is_op_class then
                         match fields with
                         | [] -> Constructors []
                         | [(id, tp, _)] ->
                            Constructors [false, (id, tp)]
                         | _ -> raise (located_loc class_id) (Failure "add_typeclass")
                       else
                         RecordDecl (None, List.map mk_record_field fields)),
                      []])
  in
  let _ = debug_printf 1 "@[add_typeclass command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc class_id, cmd)

(* Add an instance of an typeclass that is a single term *)
let add_term_instance inst_name inst_params inst_tp inst_body =
  let cmd = VernacLocal
              (false,
               VernacInstance
                 (false, inst_params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  Some (false, inst_body),
                  None))
  in
  let _ = debug_printf 1 "@[add_term_instance command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc inst_name, cmd)

(* Add an instance using the given record fields *)
let add_record_instance inst_name inst_params inst_tp inst_fields =
  let loc = located_loc inst_name in
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Decl_kinds.Explicit, inst_tp),
               Some (true,
                     CRecord (loc, None,
                              List.map (fun (id,body) -> (Ident (loc, id),body))
                                       inst_fields)),
               None)
  in
  let _ = debug_printf 1 "@[add_record_instance command:@ %a@]\n" pp_vernac cmd in
  interp (loc, cmd)

(* Begin an interactively-defined instance *)
let begin_instance ?(hook=(fun _ -> ())) inst_params inst_name inst_tp =
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Explicit, inst_tp),
               None, None)
  in
  let _ = debug_printf 1 "@[begin_instance command:@ %a@]\n" pp_vernac cmd in
  ignore
    (Classes.new_instance
       false inst_params (inst_name, Explicit, inst_tp) None ~hook:hook None)

(* Issue a Context command *)
let add_to_context params =
  let cmd = VernacContext params in
  let _ = debug_printf 1 "@[context command:@ %a@]\n" pp_vernac cmd in
  ignore (Classes.context false params)

(* Begin a new module *)
let begin_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []))

(* End the current module, which should have name mod_name *)
let end_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacEndSegment mod_name)

(* Begin a new section *)
let begin_section sect_id =
  Lib.open_section sect_id

(* End the current section *)
let end_section () =
  Lib.close_section ()

(* Perform some operation(s) inside a newly-defined module *)
let within_module mod_name f =
  let _ = begin_module mod_name in
  let ret = f () in
  let _ = end_module mod_name in
  ret

(* Add a list of hints to the typeclass_instances database *)
let add_typeclass_hints hints =
  List.iter (Hints.add_hints false ["typeclass_instances"]) hints

(* Reduce a constr using a list of reduction expressions *)
let reduce_constr reds constr =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let apply_redexpr c r =
    let (evd,r_interp) = Tacinterp.interp_redexp env !evdref r in
    let _ = evdref := evd in
    snd (fst (Redexpr.reduction_of_red_expr env r_interp) env !evdref c) in
  List.fold_left apply_redexpr constr reds

(* Reduce a constr to head normal form *)
let hnf_constr constr =
  reduce_constr [Hnf] constr

(* Reduce a constr using the "compute" reduction (which is call-by-value) *)
let compute_constr constr =
  reduce_constr
    [Cbv (Redops.make_red_flag [FBeta;FIota;FZeta;FDeltaBut []])]
    constr

(* Apply a series of reductions to a term in a parameter context, by
   interpreting the term to a constr, applying the reductions in order, and then
   going back to a term *)
let reduce_term params reds t =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let impls, ((env, ctx), imps1) =
    Constrintern.interp_context_evars env evdref params in
  let interp_term t = fst (Constrintern.interp_constr env !evdref t) in
  let uninterp_term c =
    Constrextern.with_implicits
      (Constrextern.with_arguments
         (Constrextern.extern_constr true env !evdref)) c
  in
  let apply_redexpr c r =
    let (evd,r_interp) = Tacinterp.interp_redexp env !evdref r in
    let _ = evdref := evd in
    snd (fst (Redexpr.reduction_of_red_expr env r_interp) env !evdref c) in
  uninterp_term (List.fold_left apply_redexpr (interp_term t) reds)

(* Fold some set of variables in c into equivalent terms, by taking
   folds_c, a list of pairs of constrs (c_from,c_to) where c_from is
   always a variable, and replacing all subterms of c equal to some
   c_from in folds_c with the corresponding c_to. *)
let rec fold_constr_vars folds_c c =
  (* apply_fold_var searches for a constr on the LHS of folds_c that
     equals c, and replaces c by the correponding RHS if found *)
  let rec apply_fold_var folds_c c =
    match folds_c with
    | [] -> c
    | (c_from,c_to)::folds_c' ->
       if Constr.equal c c_from then c_to else apply_fold_var folds_c' c in
  (* Lift a folding, due to a variable binding *)
  let lift_folding folds_c =
    List.map (fun (c_from,c_to) ->
              (Vars.lift 1 c_from, Vars.lift 1 c_to)) folds_c in
  (* The main body: recursively apply folds_c to the subterms of c *)
  match Constr.kind c with
  | Constr.Var _ -> apply_fold_var folds_c c
  | Constr.Rel _ -> apply_fold_var folds_c c
  | _ -> Constr.map_with_binders lift_folding fold_constr_vars folds_c c

(* Unfold the list of global references (which must all be constants,
   i.e., not constructors or type constructors), and then apply the
   given folds, which are given as a list of pairs (var,term) of a
   variable to be folded into the corresponding term (which should be
   equal). All terms are relative to the given parameters. *)
let unfold_fold_term params unfolds folds t =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let impls, ((env, ctx), imps1) =
    Constrintern.interp_context_evars env evdref params in
  let interp_term t = fst (Constrintern.interp_constr env !evdref t) in
  let uninterp_term c = Constrextern.extern_constr true env !evdref c in
  let t_constr = interp_term t in

  (* The following block of code comes from vernac_check_may_eval *)
  (*
  let sigma', t_constr = Constrintern.interp_open_constr env !evdref t in
  let sigma' = Evarconv.consider_remaining_unif_problems env sigma' in
  Evarconv.check_problems_are_solved env sigma';
  let sigma',nf = Evarutil.nf_evars_and_universes sigma' in
  let uctx = Evd.universe_context sigma' in
  let env_bl = Environ.push_context uctx env in
  let t_constr = nf t_constr in
  let _ = evdref := sigma' in
   *)

  let unfold_redfun =
    Tacred.unfoldn
      (List.map (fun gr ->
                 match gr with
                 | ConstRef c -> (Locus.AllOccurrences, EvalConstRef c)
                 | _ -> raise dummy_loc (Failure "unfold_fold_term"))
                unfolds) in
  let constr_unfolded = unfold_redfun env !evdref t_constr in

  (* This used the fold reduction, which seemed to not work right... *)
  (*
  let fold_redfun =
    Tacred.fold_commands
      (List.map (fun t -> fst (Constrintern.interp_constr env !evdref t)) folds) in
  let constr_out =
    fold_redfun env !evdref constr_unfolded in
   *)

  (* This does our own fold, defined above *)
  let folds_c =
    List.map (fun (id,t) ->
              let res_from = interp_term (mk_var (dummy_loc, id)) in
              let res_to = interp_term t in
              (*
              let _ =
                debug_printf "\nunfold_fold_term: unfolding %s to %a"
                               (Id.to_string id)
                               pp_constr_expr (uninterp_term res_to) in
               *)
             (res_from, res_to)) folds in
  let constr_out = fold_constr_vars folds_c constr_unfolded in
  let res = uninterp_term constr_out in
  (*
  let _ = debug_printf "\nunfold_fold_term: unfolded term: %a\n" pp_constr_expr
                         (uninterp_term constr_unfolded) in
   *)
  let _ = debug_printf 2 "@[unfold_fold_term: returning@ %a@]\n"
                       pp_constr_expr res in
  res

(* Test if constr is a constant equal to const *)
let constr_is_constant const constr =
  match Term.kind_of_term constr with
  | Term.Const (c, _) -> Constant.equal c const
  | _ -> false

(* Test if constr is a constructor equal to ctor *)
let constr_is_constructor ctor constr =
  match Term.kind_of_term constr with
  | Term.Construct (c, _) -> eq_constructor c ctor
  | _ -> false

(* Build the expression t1 = t2 *)
let mk_equality t1 t2 =
  CApp (dummy_loc,
        (None, mk_reference ["Coq"; "Init"; "Logic"] "eq"),
        [(t1, None); (t2, None)])

(* Build the expression id1 = id2 for identifiers id1 and id2 *)
let mk_ident_equality id1 id2 =
  mk_equality (mk_var id1) (mk_var id2)

(* Check that two terms are definitionally equal relative to the given
   parameter list, by checking that (forall params, eq_refl : t1=t2)
   is well-typed (eq_refl is the constructor for the equality type) *)
let check_equal_term params t1 t2 =
  let cmd = VernacCheckMayEval
              (None, None,
               (mkCLambdaN
                  dummy_loc
                  params
                  (CCast (dummy_loc,
                          CApp (dummy_loc,
                                (None, mk_reference
                                         ["Coq"; "Init"; "Logic"] "eq_refl"),
                                [(t1, None)]),
                          CastConv (mk_equality t1 t2)))))
  in
  let _ = debug_printf 2 "@[check_equal_term command:@ %a@]\n" pp_vernac cmd in
  try interp (dummy_loc, cmd); true
  with Type_errors.TypeError (env, err) ->
       let _ = debug_printf 1 "@[check_equal_term:@ %a@]\n" (pp_type_error env) err in
       false
     | Pretype_errors.PretypeError (env, evd, err) ->
       let _ = debug_printf 1 "@[check_equal_term:@ %a@]\n"
                            (pp_pretype_error env evd) err in
       false


(* Build an anonymous hole glob_term *)
let mk_glob_hole loc =
  Glob_term.GHole (loc, Evar_kinds.QuestionMark (Evar_kinds.Define true),
         IntroAnonymous, None)

(* Build a cast glob_term *)
let mk_glob_cast loc body tp =
  Glob_term.GCast (loc, body, CastConv tp)

(* Map function f over all subterms of a glob_term, including the glob_term
itself, doing subterms before superterms. The function f is also passed a
context argument of some arbitrary type, which is updated by the add_var
argument whenever the mapping passes inside a binder. *)
let rec map_rec_glob_constr_with_binders add_var f ctx glob =
  let add_vars vars = List.fold_right add_var vars ctx in
  (* First apply f to all subterms of glob, making sure to add_var if needed *)
  let glob_subterms =
    match glob with
    | Glob_term.GApp (loc, head, args) ->
       let head' = map_rec_glob_constr_with_binders add_var f ctx head in
       let args' =
         List.map (map_rec_glob_constr_with_binders add_var f ctx) args in
       Glob_term.GApp (loc, head', args')
    | Glob_term.GLambda (loc, nm, b_kind, tp, body) ->
       let tp' = map_rec_glob_constr_with_binders add_var f ctx tp in
       let body' =
         map_rec_glob_constr_with_binders add_var f (add_var nm ctx) body in
       Glob_term.GLambda (loc, nm, b_kind, tp', body')
    | Glob_term.GProd (loc, nm, b_kind, tp, body) ->
       let tp' = map_rec_glob_constr_with_binders add_var f ctx tp in
       let body' =
         map_rec_glob_constr_with_binders add_var f (add_var nm ctx) body in
       Glob_term.GProd (loc, nm, b_kind, tp', body')
    | Glob_term.GLetIn (loc, nm, rhs, body) ->
       let rhs' = map_rec_glob_constr_with_binders add_var f ctx rhs in
       let body' =
         map_rec_glob_constr_with_binders add_var f (add_var nm ctx) body in
       Glob_term.GLetIn (loc, nm, rhs', body')
    | Glob_term.GCases (loc, style, r_opt, scruts, clauses) ->
       let scruts_vars =
         concat_map (function
                      | (_, (as_name, None)) -> [as_name]
                      | (_, (as_name, Some (_, _, in_vars))) ->
                         as_name::in_vars) scruts in
       let r_opt' =
         Option.map
           (map_rec_glob_constr_with_binders add_var f (add_vars scruts_vars))
           r_opt
       in
       let scruts' =
         List.map (fun (tm, stuff) ->
                   (map_rec_glob_constr_with_binders add_var f ctx tm, stuff))
                  scruts in
       let clauses' =
         List.map (fun (loc, pvars, pats, body) ->
                   let ctx' = add_vars (List.map (fun x -> Name x) pvars) in
                   (loc, pvars, pats,
                    map_rec_glob_constr_with_binders add_var f ctx' body))
                  clauses in
       Glob_term.GCases (loc, style, r_opt', scruts', clauses')
    | Glob_term.GLetTuple (loc, vars, (as_var, ret_opt), rhs, body) ->
       let ret_opt' =
         Option.map (map_rec_glob_constr_with_binders
                       add_var f (add_var as_var ctx)) ret_opt in
       let rhs' = map_rec_glob_constr_with_binders add_var f ctx rhs in
       let body' =
         map_rec_glob_constr_with_binders add_var f (add_vars vars) body
       in
       Glob_term.GLetTuple (loc, vars, (as_var, ret_opt'), rhs', body')
    | Glob_term.GIf (loc, scrut, (as_var, ret_opt), sub1, sub2) ->
       let scrut' = map_rec_glob_constr_with_binders add_var f ctx scrut in
       let ret_opt' =
         Option.map (map_rec_glob_constr_with_binders
                       add_var f (add_var as_var ctx)) ret_opt in
       let sub1' = map_rec_glob_constr_with_binders add_var f ctx sub1 in
       let sub2' = map_rec_glob_constr_with_binders add_var f ctx sub2 in
       Glob_term.GIf (loc, scrut', (as_var, ret_opt'), sub1', sub2')
    | Glob_term.GRec (loc, fix_kind, _, _, _, _) ->
       raise dummy_loc (Failure "map_rec_glob_constr_with_binders: does not yet handle GRec")
    | Glob_term.GCast (loc, tm, cast) ->
       let tm' = map_rec_glob_constr_with_binders add_var f ctx tm in
       let cast' = Miscops.map_cast_type
                     (map_rec_glob_constr_with_binders add_var f ctx) cast in
       Glob_term.GCast (loc, tm', cast')
    | (Glob_term.GVar _ | Glob_term.GSort _ | Glob_term.GHole _ |
       Glob_term.GRef _ | Glob_term.GEvar _ | Glob_term.GPatVar _) as x -> x
  in
  f ctx glob_subterms

(* Replace the free variables of a glob_term using a Map *)
let replace_glob_free_vars map glob =
  map_rec_glob_constr_with_binders
    (function
      | Name x -> Id.Map.remove x
      | Anonymous -> fun map -> map)
    (fun map g ->
     match g with
     | (Glob_term.GVar (loc, x) | Glob_term.GRef (loc, VarRef x, _)) as glob ->
        (try Id.Map.find x map
         with Not_found -> glob)
     | glob -> glob)
    map
    glob


(***
 *** Building and Destructing Coq Inductive Objects
 ***)

type empty = {elim_empty: 'a . 'a}

type ('a, 'b) sum =
  | Left of 'a
  | Right of 'b

exception DescrFailedInternal
exception DescrFailed of string * Constr.t

(* Descriptions of the values of some Coq type, given as a "way" to map values
of the Coq type to and from some OCaml type: ('t,'f) constr_descr describes
how to destruct Coq values of this type to type 'to, and how to build Coq
expressions of this type from elements of type 'f. *)
type (_,_) constr_descr =
  | Descr_Ctor : constructor * (('t1,'f1) constr_array_descr) *
                   ('t2,'f2) constr_descr ->
                 (('t1,'t2) sum, ('f1,'f2) sum) constr_descr
  | Descr_Fail : (empty, empty) constr_descr
  | Descr_Constr : (Constr.t, constr_expr) constr_descr
  | Descr_Iso : string * ('t1 -> 't2) * ('f2 -> 'f1) *
                  ('t1, 'f1) constr_descr -> ('t2, 'f2) constr_descr
  | Descr_ConstrMap : (Constr.t -> Constr.t) * (constr_expr -> constr_expr) *
                        ('t, 'f) constr_descr ->
                      ('t, 'f) constr_descr
  | Descr_Rec : (('t, 'f) constr_descr -> ('t, 'f) constr_descr) ->
                ('t, 'f) constr_descr
  | Descr_Direct : (Constr.t -> 't) * ('f -> constr_expr) ->
                   ('t,'f) constr_descr
 and (_,_) constr_array_descr =
   | ArrayDescr_Nil : (unit,unit) constr_array_descr
   | ArrayDescr_Cons : ('t1,'f1) constr_descr *
                         (('t1,'f1) sum -> ('t2, 'f2) constr_array_descr) ->
                       ('t1 * 't2, 'f1 * 'f2) constr_array_descr
   | ArrayDescr_Direct : (Constr.t list -> 't) * ('f -> constr_expr list) ->
                         ('t,'f) constr_array_descr

(* Build a constr_expr from a description *)
let rec build_constr_expr : type t f. (t,f) constr_descr -> f -> constr_expr = function
  | Descr_Ctor (ctor,array_descr,descr') ->
     (function
       | Left a -> mkAppC (mk_global_expl (ConstructRef ctor),
                           build_constr_expr_list array_descr a)
       | Right b -> build_constr_expr descr' b)
  | Descr_Fail -> fun emp -> emp.elim_empty
  | Descr_Constr -> fun constr_expr -> constr_expr
  | Descr_Iso (name,iso_to, iso_from, descr') ->
     fun b -> build_constr_expr descr' (iso_from b)
  | Descr_ConstrMap (map_to, map_from, descr') ->
     fun a -> map_from (build_constr_expr descr' a)
  | Descr_Rec f -> build_constr_expr (f (Descr_Rec f))
  | Descr_Direct (f_to,f_from) -> f_from
and build_constr_expr_list : type t f. (t,f) constr_array_descr -> f -> constr_expr list = function
  | ArrayDescr_Nil -> fun () -> []
  | ArrayDescr_Cons (descr, rest) ->
     fun (a,b) -> let constr = build_constr_expr descr a in
                  constr :: build_constr_expr_list (rest (Right a)) b
  | ArrayDescr_Direct (f_to,f_from) -> f_from

(* Destruct a constr using a description *)
let rec destruct_constr : type t f. (t,f) constr_descr -> Constr.t -> t = function
  | Descr_Ctor (ctor,array_descr,descr') ->
     fun constr ->
     let destruct_ctor_app c =
       match Term.kind_of_term constr with
       | Term.App (f, args) ->
          (match Term.kind_of_term f with
           | Term.Construct (c, _) -> (c, args)
           | _ -> raise dummy_loc DescrFailedInternal)
       | Term.Construct (c, _) -> (c, [| |])
       | _ -> raise dummy_loc DescrFailedInternal
     in
     (try
         (*
         let _ =
           debug_printf
             1
             "destruct_constr:\n@[ matching constr@ %a@]\n@[ against ctor %a@]\n"
             pp_constr constr pp_constr
             (Globnames.printable_constr_of_global (ConstructRef ctor))
         in
          *)
         let (c,args) = destruct_ctor_app constr
         (* README: don't do the below: it reduces constr once for each ctor match *)
           (*
           try destruct_ctor_app constr
           with DescrFailedInternal -> destruct_ctor_app constr
            *)
         in
         if eq_constructor c ctor then
           Left (destruct_constr_array array_descr args)
         else
           Right (destruct_constr descr' constr)
       with DescrFailedInternal -> Right (destruct_constr descr' constr))
  | Descr_Fail -> fun constr -> raise dummy_loc DescrFailedInternal
  | Descr_Constr -> fun constr -> constr
  | Descr_Iso (name,iso_to, iso_from, descr') ->
     fun constr ->
     (try iso_to (destruct_constr descr' constr)
      with DescrFailedInternal -> raise dummy_loc (DescrFailed (name, constr)))
  | Descr_ConstrMap (map_to, map_from, descr') ->
     fun constr -> destruct_constr descr' (map_to constr)
  | Descr_Rec f -> destruct_constr (f (Descr_Rec f))
  | Descr_Direct (f_to,f_from) -> f_to
and destruct_constr_list : type t f. (t,f) constr_array_descr -> Constr.t list -> t = function
  | ArrayDescr_Nil -> (function
                        | [] -> ()
                        | _ -> raise dummy_loc DescrFailedInternal)
  | ArrayDescr_Cons (descr, rest) ->
     (function
       | [] -> raise dummy_loc DescrFailedInternal
       | constr::constrs ->
          let a = destruct_constr descr constr in
          (a, destruct_constr_list (rest (Left a)) constrs))
  | ArrayDescr_Direct (f_to,f_from) -> f_to
and destruct_constr_array : type t f. (t,f) constr_array_descr -> Constr.t array -> t =
  fun descr constrs -> destruct_constr_list descr (Array.to_list constrs)

(* Helpers for building descriptions *)
let nullary_ctor : 't_rest 'f_rest . string list -> string -> ('t_rest,'f_rest) constr_descr ->
                   ((unit, 't_rest) sum, (unit, 'f_rest) sum) constr_descr =
  fun dir name descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Nil, descr_rest)
let unary_ctor : 't1 'f1 't_rest 'f_rest . string list -> string ->
                 ('t1,'f1) constr_descr ->
                 ('t_rest,'f_rest) constr_descr ->
                 (('t1 * unit, 't_rest) sum,
                  ('f1 * unit, 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons (descr_a, fun _ -> ArrayDescr_Nil), descr_rest)
let binary_ctor : 't1 'f1 't2 'f2 't_rest 'f_rest . string list -> string ->
                  ('t1,'f1) constr_descr ->
                  (('t1,'f1) sum -> ('t2,'f2) constr_descr) ->
                  ('t_rest,'f_rest) constr_descr ->
                  (('t1 * ('t2 * unit), 't_rest) sum,
                   ('f1 * ('f2 * unit), 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_b descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons (descr_b a, fun _ -> ArrayDescr_Nil)),
              descr_rest)
let ternary_ctor : 't1 'f1 't2 'f2 't3 'f3 't_rest 'f_rest .
                   string list -> string ->
                   ('t1,'f1) constr_descr ->
                   (('t1,'f1) sum -> ('t2,'f2) constr_descr) ->
                   (('t1,'f1) sum -> ('t2,'f2) sum -> ('t3,'f3) constr_descr) ->
                   ('t_rest,'f_rest) constr_descr ->
                   (('t1 * ('t2 * ('t3 * unit)), 't_rest) sum,
                    ('f1 * ('f2 * ('f3 * unit)), 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_b descr_c descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons
                   (descr_b a,
                    fun b -> ArrayDescr_Cons
                               (descr_c a b, fun _ -> ArrayDescr_Nil))),
              descr_rest)
let quaternary_ctor =
  fun dir name descr_a descr_b descr_c descr_d descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons
                   (descr_b a,
                    fun b ->
                    ArrayDescr_Cons
                      (descr_c a b,
                       fun c ->
                       ArrayDescr_Cons
                         (descr_d a b c, fun _ -> ArrayDescr_Nil)))),
              descr_rest)
let quinary_ctor =
  fun dir name descr_a descr_b descr_c descr_d descr_e descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons
                   (descr_b a,
                    fun b ->
                    ArrayDescr_Cons
                      (descr_c a b,
                       fun c ->
                       ArrayDescr_Cons
                         (descr_d a b c,
                          fun d ->
                          ArrayDescr_Cons
                            (descr_e a b c d,
                             fun _ -> ArrayDescr_Nil))))),
              descr_rest)

(* Description that always reduced a constr to hnf *)
let hnf_descr (descr: ('t,'f) constr_descr) : ('t,'f) constr_descr =
  Descr_ConstrMap (hnf_constr, (fun x -> x), descr)

(* Description that always builds a hole *)
let hole_descr (descr: ('t,'f) constr_descr) : ('t, unit) constr_descr =
  Descr_Iso ("hole",
             (fun x -> x),
             (fun () -> CHole (dummy_loc, None, IntroAnonymous, None)),
             descr)

(* The module for many Coq datatypes *)
let datatypes_mod = ["Coq"; "Init"; "Datatypes"]

(* Description of the Coq Boolean type *)
let bool_descr : (bool,bool) constr_descr =
  Descr_Iso ("bool",
             (function
               | Left () -> true
               | Right (Left ()) -> false
               | Right (Right emp) -> emp.elim_empty),
             (fun b -> if b then Left () else Right (Left ())),
             (nullary_ctor datatypes_mod "true"
                           (nullary_ctor datatypes_mod "false" Descr_Fail)))

(* Description of the Coq pair type *)
let pair_descr (descr1 : ('t1,'f1) constr_descr)
               (descr2 : ('t2,'f2) constr_descr) :
      ('t1 * 't2, 'f1 * 'f2) constr_descr =
  Descr_Iso ("pair",
             (function
               | Left (tpa_ctor, (tpb_ctor, (a, (b, ())))) -> (a, b)
               | Right emp -> emp.elim_empty),
             (fun (a,b) -> Left ((), ((), (a, (b, ()))))),
             quaternary_ctor
               datatypes_mod "pair" (hole_descr Descr_Constr)
               (fun _ -> hole_descr Descr_Constr)
               (fun _ _ -> descr1) (fun _ _ _ -> descr2) Descr_Fail
            )

(* Description of the Coq option type *)
let option_descr (descr : ('t,'f) constr_descr) :
      ('t option, 'f option) constr_descr =
  Descr_Iso ("option",
             (function
               | Left (tp, (x, ())) -> Some x
               | Right (Left (tp, ())) -> None
               | Right (Right emp) -> emp.elim_empty),
             (function
               | Some x -> Left ((), (x, ()))
               | None -> Right (Left ((), ()))),
             binary_ctor
               datatypes_mod "Some" (hole_descr Descr_Constr) (fun _ -> descr)
               (unary_ctor datatypes_mod "None" (hole_descr Descr_Constr)
                           Descr_Fail))

(* Description of the Coq list type *)
let list_descr (descr : ('t,'f) constr_descr) :
      ('t list, 'f list) constr_descr =
  Descr_Rec
    (fun l_descr ->
     Descr_Iso
       ("list",
        (function
          | Left (tp, (x, (rest, ()))) -> x::rest
          | Right (Left (tp, ())) -> []
          | Right (Right emp) -> emp.elim_empty),
        (function
          | x::l -> Left ((), (x, (l, ())))
          | [] -> Right (Left ((), ()))),
        ternary_ctor
          datatypes_mod "cons" (hole_descr Descr_Constr) (fun _ -> descr)
          (fun _ _ -> hnf_descr l_descr)
          (unary_ctor datatypes_mod "nil" (hole_descr Descr_Constr) Descr_Fail)))

(* Decode a little-endian list of booleans into an int *)
let rec decode_ascii_bits bits =
  match bits with
  | [] -> 0
  | b :: bits' -> (if b then 1 else 0) + 2 * decode_ascii_bits bits'

(* Encode an int into a little-endian list of booleans of length n *)
let rec encode_ascii_bits n i =
  if n = 0 then [] else
    (i mod 2 > 0) :: encode_ascii_bits (n-1) (i/2)

(* Description of the Coq Ascii type *)
let ascii_descr : (char, char) constr_descr =
  Descr_Iso
    ("ascii",
     (function
       | Left c -> c
       | Right emp -> emp.elim_empty),
     (fun c -> Left c),
     Descr_Ctor
       (mk_constructor dummy_loc ["Coq"; "Strings"; "Ascii"] "Ascii",
        (ArrayDescr_Direct
           ((fun args ->
             if List.length args = 8 then
               char_of_int (decode_ascii_bits
                              (List.map (destruct_constr bool_descr) args))
             else
               raise dummy_loc DescrFailedInternal),
            (fun c ->
             List.map (fun b ->
                       mk_reference datatypes_mod (if b then "true" else "false"))
                      (encode_ascii_bits 8 (int_of_char c))))
         : (char, char) constr_array_descr),
        Descr_Fail))

(* Description of the Coq string type *)
let string_descr : (string, string) constr_descr =
  Descr_Rec
    (fun str_descr ->
     Descr_Iso
       ("string",
        (function
          | Left (c, (l, ())) -> (String.make 1 c)^l
          | Right (Left ()) -> String.make 0 'a'
          | Right (Right emp) -> emp.elim_empty),
        (fun str ->
         let len = String.length str in
         if len > 0 then
           Left (String.get str 0, (String.sub str 1 (len-1), ()))
         else
           Right (Left ())),
        binary_ctor
          ["Coq"; "Strings"; "String"] "String" ascii_descr
          (fun _ -> hnf_descr str_descr)
          (nullary_ctor ["Coq"; "Strings"; "String"] "EmptyString" Descr_Fail)))

(* An optimized description of the Coq string type, that converts strings
directly to string literals instead of cons-list expressions *)
let string_fast_descr : (string, string) constr_descr =
  Descr_Direct
    (destruct_constr string_descr,
     (fun str ->
      CDelimiters (dummy_loc, "string",
                   CPrim (dummy_loc, String str))))

let mk_string = build_constr_expr string_fast_descr
