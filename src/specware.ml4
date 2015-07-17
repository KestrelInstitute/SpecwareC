
DECLARE PLUGIN "specware"

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

(* Map f over an option type *)
let map_opt f opt =
  match opt with
  | Some x -> Some (f x)
  | None -> None

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
let mk_var id = CRef (Ident id, None)

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
  mk_ref_app_named_args loc (Ident id) args

(* Build a qualified id (NOTE: dir is *not* reversed here) *)
let mk_qualid dir id =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) id

(* Cons an id onto the end of a qualid *)
let qualid_cons qualid id =
  let (mod_path,mod_name) = repr_qualid qualid in
  make_qualid (DirPath.make ([mod_name] @ DirPath.repr mod_path)) id

(* Build a term for a global constant, where dir lists the module path
   as a list (e.g., ["Coq"; "Init"; "Logic"]) and id is the id *)
let mk_reference dir id =
  CRef (Qualid (dummy_loc, mk_qualid dir id), None)

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
(* FIXME: find a better way than using strings! *)
let qualid_of_global gr =
  qualid_of_string (global_to_string gr)

(* Build an expression for a global applied to named implicit args *)
let mk_global_app_named_args gr args =
  mk_ref_app_named_args dummy_loc (Qualid (dummy_loc, qualid_of_global gr)) args

(* Build an exprssion for a global with @ in front of it *)
let mk_global_expl gr =
  CAppExpl (dummy_loc,
            (None, (Qualid (dummy_loc, qualid_of_global gr)), None),
            [])

(* Look up a defined constant by qualid *)
(* FIXME: raise a different exception if the qualid is not a constant... *)
let lookup_constant loc qualid =
  match Nametab.locate qualid with
  | ConstRef c -> c
  | _ -> raise loc Not_found

(* Look up an identifier in the current module and make it fully qualified *)
let qualify_identifier id =
  let _ = debug_printf 2 "@[qualify_identifier: %s@]\n" (Id.to_string id) in
  qualid_of_global (Nametab.locate (qualid_of_ident id))

(* Build the expression t1 = t2 *)
let mk_equality t1 t2 =
  CApp (dummy_loc,
        (None, mk_reference ["Coq"; "Init"; "Logic"] (Id.of_string "eq")),
        [(t1, None); (t2, None)])

(* Build the expression id1 = id2 for identifiers id1 and id2 *)
let mk_ident_equality id1 id2 =
  mk_equality (mk_var id1) (mk_var id2)

(* Build the expression t1::t2::...::tn::nil *)
let mk_list loc ts =
  List.fold_right
    (fun t rest ->
     mkAppC (mk_reference ["Coq"; "Init"; "Datatypes"] (Id.of_string "cons"),
             [t; rest]))
    ts
    (mk_reference ["Coq"; "Init"; "Datatypes"] (Id.of_string "nil"))

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

(* Make an implicit {name:tp} assumption, where name is an id and tp
   is a construction (type constr) *)
let mk_implicit_assum name tp =
  LocalRawAssum ([(Loc.dummy_loc, Name name)], Default Implicit, tp)

(* Add a definition to the current Coq image *)
let add_definition id params type_opt body =
  let cmd = VernacDefinition
              ((None, Definition), id,
               DefineBody (params, None, body, type_opt))
  in
  let _ = debug_printf 1 "@[add_definition command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc id, cmd)

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
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Decl_kinds.Explicit, inst_tp),
               Some (false, inst_body),
               None)
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
                                (None, mk_reference ["Coq"; "Init"; "Logic"]
                                                    (Id.of_string "eq_refl")),
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

(***
 *** Global and local references to specs
 ***)

(* FIXME: figure out how to get good error messages in the lookup
   functions! *)

(* A local reference to a spec is a qualid pointing to its module *)
type spec_locref = qualid

(* Build a spec_locref from a reference *)
let spec_locref_of_ref r = located_elem (qualid_of_reference r)

(* Build a spec_locref from a local identifier *)
let spec_locref_of_id id = qualid_of_ident id

(* Get the "basename" of a locref, i.e., the last Id in the path *)
let spec_locref_basename locref =
  let _,base = repr_qualid locref in
  base

(* Return a qualid that points to field fname in spec locref *)
let field_in_spec locref fname =
  qualid_cons locref fname

(* Return a local reference to the axiom typeclass of a spec given by
   a local reference *)
let spec_typeclass_qualid locref =
  qualid_cons locref (spec_locref_basename locref)

let spec_typeclass_ref loc locref =
  Qualid (loc, spec_typeclass_qualid locref)

(* A global reference to a spec is a global reference to the spec's
   module *)
type spec_globref = module_path

(* Compare spec globrefs for equality *)
let spec_globref_equal (g1  : spec_globref) (g2 : spec_globref) =
  ModPath.equal g1 g2

(* Lookup the global reference to a spec from a local reference *)
let lookup_spec_globref locref =
  try
    Nametab.locate_module locref
  with Not_found ->
    (* FIXME: put in a location here *)
    user_err_loc (dummy_loc, "_",
                  str ("Could not find spec " ^ string_of_qualid locref))

(* Return a global reference to the current spec *)
(*
let this_spec_globref () = ??
 *)

(* Turn the global reference to a spec into a local reference *)
(* FIXME: find a better way than going through strings... *)
let spec_globref_to_locref spec_globref =
  qualid_of_string (ModPath.to_string spec_globref)

(* Build a reference to a field in a global spec *)
(* FIXME: this should not go through a locref *)
let field_in_global_spec globref fname =
  field_in_spec (spec_globref_to_locref globref) fname

(* Build a reference to the axiom typeclass of a global spec *)
let global_spec_typeclass_ref loc globref =
  spec_typeclass_ref loc (spec_globref_to_locref globref)

let global_field_in_global_spec globref fname =
  Nametab.locate (field_in_global_spec globref fname)


(***
 *** Identifiers and Identifier Suffixes
 ***)

(* Build the identifier used to quantify over a field as a local
   variable *)
let field_param_id f = add_suffix f "param"

(* Get the identifier used locally for the type of a field *)
let field_type_id f = add_suffix f "type"

(* Get the identifier used locally for the type-class of a field *)
let field_class_id f = add_suffix f "class"

(* Get the identifier used for the proof of a field predicate *)
let field_proof_id f = add_suffix f "proof"

(* The name of the instance associated with a field *)
let field_inst_id f = add_suffix f "inst"

(* The axiom typeclass field pointing to an instance of this axiom *)
let field_axelem_id f = add_suffix f "axiom"

(* The name of the Spec representation of a spec named s_id *)
let spec_repr_id s_id = add_suffix s_id "repr"

(* The name of the IsoToSpec proof for a spec named s_id *)
let spec_iso_id s_id = add_suffix s_id "iso"

(* The variable name for the implicit spec argument of a morphism instance *)
let morph_spec_arg_id = Id.of_string "Spec"


(***
 *** Operations on Specs
 ***)

(* A spec contains its name, its module path, and its op and axiom names. Note
that ops and axioms --- collectively called the "fields" of the spec --- are
stored in reverse order, for efficiency of adding new ones. *)
type spec = {
  spec_name : Id.t;
  spec_path : DirPath.t;
  spec_ops : (Id.t * constr_expr * constr_expr option) list;
  spec_axioms : (Id.t * constr_expr) list
}

(* Create an empty spec with the given name *)
let make_empty_spec spec_id =
  { spec_name = spec_id; spec_path = Lib.cwd_except_section ();
    spec_ops = []; spec_axioms = [] }

(* Whether spec contains an op or axiom named f *)
let contains_field spec f =
  List.exists (fun (f',_,_) -> Id.equal f f') spec.spec_ops ||
    List.exists (fun (f', _) -> Id.equal f f') spec.spec_axioms

(* Check that a field (op or axiom) of the given name exists in spec *)
let spec_field_exists ?(suffix="class") spec f =
  let res = Nametab.exists_cci (Lib.make_path f) in
  let _ = debug_printf 2 "@[spec_field_exists (%s): %B@]\n" (Id.to_string f) res in
  res

(* Remove fields that no longer exist (because of potential Undos) *)
let filter_nonexistent_fields spec =
  { spec with
    spec_ops = List.filter (fun (id, _,_) ->
                            spec_field_exists spec id) spec.spec_ops;
    spec_axioms = List.filter (fun (id,_) -> spec_field_exists spec id) spec.spec_axioms }


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = ref (MPmap.empty)

(* Register a global spec in the spec_table *)
let register_spec spec_globref spec =
  spec_table := MPmap.add spec_globref spec !spec_table

(* Look up a spec from a global reference to it *)
let lookup_global_spec globref =
  MPmap.find globref !spec_table

(* Look up a spec and its spec_globref from a local spec reference *)
let lookup_spec_and_globref locref =
  let globref = lookup_spec_globref locref in
  (lookup_global_spec globref, globref)

(* Look up a spec from a local spec reference *)
let lookup_spec locref = fst (lookup_spec_and_globref locref)


(***
 *** Representing Specs as Inductive Objects
 ***)

(* Create the term (Spec_ConsOp f tp oppred (fun (f:f__class) f__pf => rest)) *)
let repr_cons_op loc rest (f, tp, oppred) : constr_expr =
  mkAppC (mk_reference ["Specware"; "Spec"] (Id.of_string "Spec_ConsOp"),
          [CPrim (loc, String (Id.to_string f)); tp;
           (match oppred with
            | None -> mk_reference ["Coq"; "Init"; "Datatypes"]
                                   (Id.of_string "None")
            | Some pred ->
               mkAppC (mk_reference ["Coq"; "Init"; "Datatypes"]
                                    (Id.of_string "Some"),
                       [pred]));
           (mkCLambdaN loc
                       [LocalRawAssum ([loc, Name f], Default Explicit,
                                       mk_var (loc, field_class_id f));
                        LocalRawAssum ([loc, Name (field_proof_id f)], Default Explicit,
                                       CHole (loc, None, IntroAnonymous, None))]
                       rest)
          ])

(* Create the term Spec_Axioms [("ax1",ax_tp1), ...] *)
let repr_axioms loc axioms : constr_expr =
  mkAppC (mk_reference ["Specware"; "Spec"] (Id.of_string "Spec_Axioms"),
          [mk_list loc
                   (List.rev_map
                      (fun (ax_id,ax_tp) ->
                       mkAppC (mk_reference ["Specware"; "Spec"]
                                            (Id.of_string "ax_pair"),
                               [CPrim (loc, String (Id.to_string ax_id));
                                ax_tp]))
                      axioms)])

(* Build a term of thype Spec that represents a spec *)
let build_spec_repr loc spec : constr_expr =
  List.fold_left (repr_cons_op loc)
                 (repr_axioms loc spec.spec_axioms) spec.spec_ops


(***
 *** Building Up the Current Spec
 ***)

(* The currrent spec being defined, if one exists *)
let current_spec : spec option ref = ref None

(* There is no current spec *)
exception NoCurrentSpec

(* There is already a current spec *)
exception CurrentSpecExists

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Field already exists in the current spec *)
exception FieldExists of Id.t

(* Ensure that current_spec is up-to-date with the current image, dealing with
possible Undos by the user *)
let validate_current_spec loc =
  match !current_spec with
  | None -> ()
  | Some spec ->
     (* Check that we are still in the spec's module *)
     if DirPath.equal spec.spec_path (Lib.cwd_except_section ()) then
       current_spec := Some (filter_nonexistent_fields spec)
     else if Nametab.exists_dir spec.spec_path then
       (* If the spec's module still exists but is not the current module, then
       the user is messing with us (FIXME: better error message!) *)
       raise loc (Failure "validate_current_spec")
     else
       (* If the module for the current spec no longer exists, it was
          probably removed by an Undo, so reset to no current spec *)
       current_spec := None

(* Get the current spec, raising an exception if there is none *)
let get_current_spec loc =
  let _ = validate_current_spec loc in
  match !current_spec with
  | Some spec -> spec
  | None -> raise loc NoCurrentSpec

(* Update the current spec, if it exists, by applying f *)
let update_current_spec loc f =
  let _ = validate_current_spec loc in
  match !current_spec with
  | Some spec -> current_spec := Some (f spec)
  | None -> raise loc NoCurrentSpec

(* Add a field (op or axiom) to the current spec *)
let add_spec_field axiom_p field_name tp pred_opt =
  let f = located_elem field_name in
  let loc = located_loc field_name in
  update_current_spec
    loc
    (fun spec ->
     (* First, check that the given field name does not already exist *)
     let _ = if contains_field spec f then
               raise loc (FieldExists f)
             else ()
     in
     (* Add a type-class f__class : Type := f : op_type *)
     let _ = add_typeclass (loc, field_class_id f) true false []
                           [((loc, f), tp, false)]
     in
     if axiom_p then
       (* For axioms, just add the field name to the list of axioms *)
       { spec with spec_axioms = (f,tp)::spec.spec_axioms }
     else
       (* For ops, add f__params : f__class to the context *)
       let _ =
         Classes.context false [mk_implicit_assum
                                  (field_param_id f)
                                  (mk_var (loc, field_class_id f))] in
       (* Test for an op predicate *)
       let _ =
         match pred_opt with
         | Some pred ->
            (* If there is an op predicate, add f__proof : pred to the context *)
            let _ =
              Classes.context false [mk_implicit_assum (field_proof_id f) pred]
            in true
         | None -> false
       in
       { spec with spec_ops = (f,tp,pred_opt)::spec.spec_ops })

(* Complete the current spec, by creating its axiom type-class, registering it
   in the global spec table, and creating representation as a Spec object. NOTE:
   this needs to be called after the spec's section is closed, but before its
   module is closed. *)
let complete_spec loc =
  let spec = get_current_spec loc in
  (* First, build the axioms into fields for the axiom type-class *)
  let ax_fields =
    List.rev_map
      (fun (ax_id, ax_tp) -> ((loc, field_axelem_id ax_id),
                              mk_var (loc, field_class_id ax_id),
                              true))
      spec.spec_axioms
  in
  (* Next, build parameters for all the ops and their subtype predicates. NOTE:
  we do this explicitly, rather than implicitly relying on the context, so that
  we can ensure all of the ops become params *)
  let op_params =
    List.concat
      (List.rev_map
         (fun (op_id, op_tp, pred_opt) ->
          let op_param =
            mk_implicit_assum (field_param_id op_id)
                              (mk_var (loc, field_class_id op_id)) in
          match pred_opt with
          | None -> [op_param]
          | Some pred ->
             [op_param; mk_implicit_assum (field_proof_id op_id) pred])
         spec.spec_ops)
  in
  let _ = add_typeclass (loc, spec.spec_name) false true op_params ax_fields in
  (* FIXME: register_spec should be a hook function for add_typeclass *)
  let spec_globref =
    global_modpath (Nametab.locate (qualid_of_ident spec.spec_name))
  in
  let _ = register_spec spec_globref spec in
  let _ = add_definition (loc, spec_repr_id spec.spec_name) [] None
                         (build_spec_repr loc spec) in
  let _ = add_term_instance
            (loc, Name spec_iso_id spec.spec_name) []
            (mkAppC (mk_reference ["Specware"; "Spec"]
                                  (Id.of_string "IsoToSpec"),
                     [mk_var (loc, spec_repr_id spec.spec_name);
                      CAppExpl
                        (loc, (None, Ident (loc, spec.spec_name), None), [])]))
            (CHole (loc, None, IntroAnonymous,
                    Some (Genarg.in_gen
                            (Genarg.rawwit Constrarg.wit_tactic)
                            (Tacexpr.TacArg
                               (loc,
                                Tacexpr.TacCall
                                  (loc,
                                   Qualid (loc,
                                           mk_qualid ["Specware"; "Spec"]
                                                     (Id.of_string "prove_spec_iso")),
                                   []))))))
  in
  ()

(* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  let loc = located_loc spec_lid in
  let spec_id = located_elem spec_lid in
  let _ = validate_current_spec loc in
  if !current_spec = None then
    let _ = begin_module spec_lid in
    let _ = begin_section spec_id in
    current_spec := Some (make_empty_spec spec_id)
  else
    raise loc CurrentSpecExists

(* Finish the interactive definition of a new spec by completing it
   and clearing current_spec; return the newly defined spec *)
let end_new_spec spec_lid =
  let loc = located_loc spec_lid in
  let spec_id = located_elem spec_lid in
  match !current_spec with
  | Some spec ->
     (* FIXME: make sure there aren't any other opened sections *)
     if Id.equal spec.spec_name spec_id then
       let _ = end_section () in
       let _ = complete_spec loc in
       let _ = end_module spec_lid in
       current_spec := None
     else
       raise loc WrongCurrentSpecName
  | None -> raise loc NoCurrentSpec


(***
 *** Additions to the Coq parser
 ***)

(* Run f, catching any exceptions and turning them into user_errors *)
(* FIXME: actually write this! *)
let reporting_exceptions f =
  f ()

(* FIXME: get the locations of all the identifiers right! *)

(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec

  (* Start an interactive spec definition *)
  | [ "Spec" ident(spec_name) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            begin_new_spec (dummy_loc, spec_name)) ]

  (* End an interactive spec definition *)
  | [ "Spec" "End" ident(spec_name) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            ignore (end_new_spec (dummy_loc, spec_name))) ]

  (* Add a declared op *)
  | [ "Spec" "Variable" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field false (dummy_loc,id) tp None) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" ident(id) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            add_spec_field false (dummy_loc,id) tp
                           (Some (mk_equality (mk_var (dummy_loc,id)) body))) ]

  (* Add a defined op without a type *)
  (* FIXME: figure out how to handle defs with no type... *)
(*
  | [ "Spec" "Definition" ident(id) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) None body) ]
 *)

  (* Add an axiom *)
  | [ "Spec" "Axiom" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field true (dummy_loc,id) tp None) ]

  (* Import a spec term *)
  (* FIXME HERE: add imports!! *)
  (*
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term dummy_loc st) ]
   *)
END

(* Top-level syntax for morphisms *)
(*
VERNAC COMMAND EXTEND Morphism
  (* Define a named morphism with the given name translation *)
  | [ "Spec" "Morphism" ident(morph_name) ":" global(s1) "->" global(s2)
             "{" name_translation(xlate) "}" ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity, [morph_name]),
          Vernacexpr.VtLater) ]
    -> [ start_morphism (dummy_loc, morph_name) s1 s2 xlate ]

  (* Define a named morphism with no name translation *)
  | [ "Spec" "Morphism" ident(morph_name) ":" global(s1) "->" global(s2) ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity, [morph_name]),
          Vernacexpr.VtLater) ]
    -> [ start_morphism (dummy_loc, morph_name) s1 s2 [] ]
END
 *)
