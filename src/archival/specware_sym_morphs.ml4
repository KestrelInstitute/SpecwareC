
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

(* The name of the instance associated with a field *)
let field_inst_id f = add_suffix f "inst"

(* The axiom typeclass field pointing to an instance of this axiom *)
let field_axelem_id f = add_suffix f "axiom"

(* The variable name for the implicit spec argument of a morphism instance *)
let morph_spec_arg_id = Id.of_string "Spec"


(***
 *** Field Terms and Substitutions
 ***)

(* FIXME HERE: use glob_term in place of constr_expr *)

(* A field term (or term used in a spec field) is a essentially an expression
with a set of its free variables marked as fields. Field substitution into field
terms is lazy: substitutions are accumulated in field_term_subst. *)
type field_term =
    { field_term_body : constr_expr;
      field_term_init_args : Id.t list;
      field_term_subst : field_subst
      (* field_term_module : ModPath.t option *) }

(* A field substitution maps field names to field names, possibly adding
definitions to fields *)
 and field_subst = (Id.t * Id.t * field_term option) list

(* Make the identity substitution on the given fields *)
let mk_id_subst fields = List.map (fun id -> (id, id, None)) fields

(* Make a field term from a constr_expr and a list of potential fields *)
(* FIXME: think about how to handle derived variables, e.g., f__var *)
let mk_field_term fields body =
  (*
  let free_vars = free_vars_of_constr_expr body in
  let true_fields = List.filter (fun v -> Id.Set.mem v free_vars) fields in
   *)
  let rec fixup_free_vars var_set = function
    | CRef (Ident (loc,id),us) as expr ->
       if Id.Set.mem id var_set then expr else
         CRef (Qualid (loc, qualify_identifier id), us)
    | expr ->
       map_constr_expr_with_binders Id.Set.add fixup_free_vars var_set expr
  in
  let var_set =
    List.fold_left (fun set id ->
                    Id.Set.add id (Id.Set.add (field_param_id id) set))
                   Id.Set.empty fields in
  { field_term_body = fixup_free_vars var_set body;
    field_term_init_args = fields;
    field_term_subst = mk_id_subst fields }

(* Make the substitution that adds definition d to id for each (id,d) in defs *)
let make_subst_for_defs defs : field_subst =
  List.map (fun (id, d) -> (id, id, Some d)) defs

(* Apply a field substitution to a field, returning a pair of the new field name
and the added definition for that field, if any *)
let rec subst_id subst id =
  match subst with
  | [] -> (id, None)
  | (id_from, id_to, defn_opt) :: subst' ->
     if Id.equal id_from id then (id_to, defn_opt) else subst_id subst' id

(* Get the free fields in a field term, i.e., the free variables that are
intended to be used as fields *)
let rec field_term_free_fields t =
  field_subst_free_fields t.field_term_subst
and field_subst_free_fields subst =
  List.fold_left (fun fs (_, id_to, defn_opt) ->
                  Id.Set.add id_to
                             (match defn_opt with
                              | Some defn -> Id.Set.union fs (field_term_free_fields defn)
                              | None -> fs))
                 Id.Set.empty subst

(* The argument fields of a field_term, substituted by the subst *)
let field_term_args t =
  List.map (fun id -> fst (subst_id t.field_term_subst id))
           t.field_term_init_args

(* Convert a field substitution to a map from Ids to constr_exprs *)
let field_subst_to_id_map ?(field_params=false) subst =
  List.fold_left
    (fun id_map (id_from, id_to, _) ->
     Id.Map.add id_from
                (if field_params then field_param_id id_to else id_to)
                id_map)
    Id.Map.empty subst

(* Convert a map on Ids to a field_subst *)
(*
let field_subst_of_id_map map =
  Id.Map.fold (fun id_from id_to subst -> (id_from, id_to, None) :: subst) map []
 *)

(* Convert a field_term to a constr_expr by applying the substitution. If
field_params is true, then use f__param in place of each field f. *)
let rec field_term_to_expr ?(field_params=false) t =
  replace_vars_constr_expr
    (field_subst_to_id_map ~field_params:field_params t.field_term_subst)
    t.field_term_body

(* An attempt to define the given field when it is already defined *)
exception FieldAlreadyDefined of Id.t

(* Apply a field substitution to a field term *)
let rec subst_field_term (subst: field_subst) t =
  { t with field_term_subst = compose_substs subst t.field_term_subst }

(* Compose a substitution with another one. NOTE: we assume the domain of the
substitution includes all the fields we care about, so we do not add mappings
from s2 to the end of s1 *)
and compose_substs (s2 : field_subst) (s1 : field_subst) : field_subst =
  List.map (fun (id_from, id_to, defn_opt) ->
            let (id_to_out, defn_opt') = subst_id s2 id_to in
            let defn_opt_out =
              match (defn_opt, defn_opt') with
              | (Some defn, None) -> Some (subst_field_term s2 defn)
              | (None, _) -> defn_opt'
              | _ ->
                 (* NOTE: this should never happen: should be caught earlier *)
                 raise dummy_loc (FieldAlreadyDefined id_to)
            in
            (id_from, id_to_out, defn_opt_out)) s1
  (* Any fields not already mapped by s1 can be mapped by s2 *)
  (*
  @ List.filter (fun (id, _, _) ->
                 not (List.exists (fun (id', _, _) -> Id.equal id id') s1)) s2
   *)


(***
 *** Field Contexts
 ***)

(* A field context specifies a list of named fields, each of which has a type
   and an optional definition. Fields corresponding to declared (but not
   defined) ops also have a "parameter type", which is the type used when
   quantifying over potential definitions of the op in a model.

   NOTE: field contexts are stored backwards, in that the "earlier" fields are
   stored later in the list; i.e., fields can only refer to fields later in a
   field context. This is to make it easy to add new fields as we go *)
type fctx_elem =
    { felem_id : Id.t;
      felem_type : field_term;
      felem_ptype : field_term option;
      felem_defn : field_term option
    }
type fctx = fctx_elem list

(* The empty field context *)
let empty_fctx = []

(* Return true iff an fctx_elem is defined *)
let fctx_elem_has_def elem =
  match elem.felem_defn with
  | Some _ -> true
  | None -> false

(* Get the fields referenced by the args in an fctx_elem *)
let fctx_elem_free_fields elem =
  let deps_tp = field_term_free_fields elem.felem_type in
  match elem.felem_defn with
  | Some d -> Id.Set.union deps_tp (field_term_free_fields d)
  | None -> deps_tp

(* Find a named field in an fctx, returning None if not found *)
let rec fctx_lookup fctx f =
  match fctx with
  | [] -> None
  | elem :: fctx' ->
     if Id.equal f elem.felem_id then
       Some elem
     else
       fctx_lookup fctx' f

(* Print an fctx_elem to a string, for debugging purposes *)
let fctx_elem_to_string elem : string =
  match elem.felem_defn with
  | None ->
     Format.sprintf "%s : %s" (Id.to_string elem.felem_id)
                    (constr_expr_to_string
                       (field_term_to_expr elem.felem_type))
  | Some defn ->
     Format.sprintf "%s : %s := %s" (Id.to_string elem.felem_id)
                    (constr_expr_to_string
                       (field_term_to_expr elem.felem_type))
                    (constr_expr_to_string
                       (field_term_to_expr defn))

(* Print an fctx to a string, for debugging purposes *)
let rec fctx_to_string ?(recursive_p=false) fctx =
  if recursive_p then
    match fctx with
    | [] -> ""
    | [elem] -> fctx_elem_to_string elem
    | elem :: fctx' ->
       Format.sprintf "%s, %s" (fctx_elem_to_string elem)
                      (fctx_to_string ~recursive_p:true fctx')
  else
    Printf.sprintf "{%s}" (fctx_to_string ~recursive_p:true fctx)

(* Build a field_term relative to an fctx *)
let mk_fctx_term fctx body =
  mk_field_term (List.rev_map (fun elem -> elem.felem_id) fctx) body

(* Cons a field to a field context *)
let fctx_cons id tp ptype_opt defn_opt fctx =
  { felem_id = id; felem_type = tp;
    felem_ptype = ptype_opt; felem_defn = defn_opt } :: fctx

(* Convert a single fctx_elem to an implicit assumption, or to None if it is not
quantified (indicated by having felem_ptype = None). If use_classes is false,
use felem_type instead of ptype, but still only include those elements that have
felem_ptype defined. *)
let fctx_elem_to_param loc ?(use_classes=true) elem =
  match elem.felem_ptype with
  | Some tp ->
     if use_classes then
       Some (mk_implicit_assum
               (field_param_id elem.felem_id)
               (field_term_to_expr ~field_params:true tp))
     else
       Some (mk_implicit_assum elem.felem_id (field_term_to_expr elem.felem_type))
  | None -> None

(* Convert an fctx to a list of class parameters, one for each field
   in the context (remember: fctx is reversed) *)
let fctx_params loc ?(use_classes=true) fctx =
  rev_filter_map (fctx_elem_to_param loc ~use_classes:use_classes) fctx

(* Convert an fctx to a list of implicit arguments (f:=f), including only
parameter fields (that has felem_ptype defined) *)
let fctx_to_args loc fctx =
  rev_filter_map (fun elem ->
                  if elem.felem_ptype = None then None else
                    Some (field_param_id elem.felem_id,
                          mk_var (loc, elem.felem_id))) fctx

(* Check the equality of two field terms relative to fctx *)
let check_equal_field_term loc fctx d1 d2 =
  check_equal_term (fctx_params loc ~use_classes:false fctx)
                   (field_term_to_expr d1) (field_term_to_expr d2)

(* Apply f to any field name shared by fctx1 and fctx2 *)
let fctx_iter_shared_fields f fctx1 fctx2 =
  List.iter (fun elem1 ->
             match fctx_lookup fctx2 elem1.felem_id with
             | Some _ -> f elem1.felem_id
             | None -> ()) fctx1

(* Filter an fctx to include only the given set of fields and all the fields on
which they recursively depend. NOTE: remember that fctxs are stored backwards,
so that fields can only depend on those occuring *later* in the list. *)
let rec filter_fctx fields fctx =
  match fctx with
  | [] -> []
  | elem :: fctx' ->
     if Id.Set.mem elem.felem_id fields
        || Id.Set.mem (field_param_id elem.felem_id) fields
     then
       elem :: filter_fctx (Id.Set.union (fctx_elem_free_fields elem) fields)
                           fctx'
     else
       filter_fctx fields fctx'

(* Add a definition to the current module / spec, relative to the given
   fctx. Return a pair of field_terms, one for the type of the new definition
   and one for the new definition itself. *)
let add_local_definition loc (fctx : fctx) id type_opt body =
  let (tp, free_vars) =
    match type_opt with
    | Some tp ->
       (tp, Id.Set.union (free_vars_of_constr_expr tp)
                         (free_vars_of_constr_expr body))
    | None ->
       (CHole (loc, None, IntroIdentifier id, None),
        free_vars_of_constr_expr body)
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  let _ = add_definition (loc, id) (fctx_params loc fctx_free_vars) (Some tp) body in
  (mk_fctx_term fctx_free_vars tp,
   mk_fctx_term fctx_free_vars body)

(* Add an operational type class to the current module / spec, relative to the
   given fctx. Return two field_terms, the first is just the type tp itself
   while the second uses the new type class *)
let add_local_op_typeclass loc fctx class_id field_id is_prop_class tp =
  let free_vars = free_vars_of_constr_expr tp in
  let _ =
    debug_printf 2 "add_local_op_typeclass for id %s: free vars = %s\n"
                 (Id.to_string class_id)
                 (Id.Set.fold (fun v str ->
                               Printf.sprintf "%s,%s" (Id.to_string v) str)
                              free_vars "")
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  let _ = add_typeclass (loc, class_id) true is_prop_class
                        (fctx_params loc fctx_free_vars)
                        [((loc, field_id), tp, false)] in
  (mk_fctx_term fctx_free_vars tp,
   mk_fctx_term fctx_free_vars
                (mk_id_app_named_args loc (loc, class_id)
                                      (fctx_to_args loc fctx_free_vars)))

(* Add a type class to the current module / spec, relative to the given fctx,
   and return a field_term for the new type class *)
let add_local_record_typeclass loc fctx id is_prop_class fields =
  let _ = add_typeclass (loc, id) false is_prop_class
                        (fctx_params loc fctx) fields
  in
  mk_fctx_term fctx (mk_id_app_named_args loc (loc, id) (fctx_to_args loc fctx))

(* Add a typeclass instance to the current module / spec *)
let add_local_term_instance loc fctx id tp body =
  let free_vars =
    Id.Set.union (free_vars_of_constr_expr tp) (free_vars_of_constr_expr body)
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  add_term_instance (loc, id) (fctx_params loc fctx_free_vars) tp body

(* Add a record-based typeclass instance to the current module / spec *)
let add_local_record_instance loc fctx id tp fields =
  let free_vars =
    List.fold_left (fun free_vars (_, body) ->
                    Id.Set.union (free_vars_of_constr_expr body) free_vars)
                   (free_vars_of_constr_expr tp) fields
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  add_record_instance (loc, id) (fctx_params loc fctx_free_vars) tp fields


(***
 *** Merging and substituting into global field contexts
 ***)

(* FIXME HERE: extract common functionality from merge_fctxs and subst_fctx *)

(* Either the types (if flag = false) or the definitions (if flag = true) of the
same field are different in two contexts that are supposed to be compatible *)
exception FieldMismatch of Id.t * bool

(* Merge two fctxs, merging any fields that they share. Also check that the two
fctxs are compatible, meaning that any shared fields have the same types and
definitions; raise FieldMismatch if not. *)
let merge_fctxs loc base_fctx fctx1 fctx2 =
  (* First, build a list of all the field names and their dependencies *)
  let names_and_deps =
    (List.map (fun elem1 ->
               (elem1.felem_id,
                Id.Set.elements
                  (match fctx_lookup fctx2 elem1.felem_id with
                   | Some elem2 -> Id.Set.union (fctx_elem_free_fields elem1)
                                                (fctx_elem_free_fields elem2)
                   | None -> fctx_elem_free_fields elem1)))
              fctx1)
    @ (filter_map (fun elem2 -> match fctx_lookup fctx1 elem2.felem_id with
                                | None -> Some (elem2.felem_id,
                                                Id.Set.elements
                                                  (fctx_elem_free_fields elem2))
                                | Some _ -> None) fctx2)
  in
  (* Next, sort the names *)
  let sorted_names_and_deps =
    try
      stable_topo_sort loc fst Id.equal snd names_and_deps
    with TopoCircularity i ->
      (* FIXME: use a better exception here *)
      raise loc (Failure ("merge_fctxs: circular dependency for field "
                          ^ Id.to_string (fst (List.nth names_and_deps i))
                          ^ "; field deps = "
                          ^ String.concat
                              ", "
                              (List.map
                                 (fun (id, deps) ->
                                  Id.to_string id ^ " -> {"
                                  ^ String.concat "," (List.map Id.to_string deps)
                                  ^ "}") names_and_deps)))
  in
  (* Now build up the context to return starting at the right, because fctxs are
  stored in reverse order (inner-most bindings last) *)
  List.fold_right
    (fun (f, _) fctx ->
     let _ = debug_printf 2 "@[%s@ %s@]\n"
                          "merge_fctxs: adding id" (Id.to_string f)
     in
     let new_elem =
       match (fctx_lookup fctx1 f, fctx_lookup fctx2 f) with
       | (Some elem1, None) -> elem1
       | (None, Some elem2) -> elem2
       | (Some elem1, Some elem2) ->
          let _ = if not (check_equal_field_term
                            loc (fctx @ base_fctx)
                            elem1.felem_type elem2.felem_type) then
                    raise loc (FieldMismatch (f, false)) else ()
          in
          let defn_opt =
            (match (elem1.felem_defn, elem2.felem_defn) with
             | (Some d1, None) -> Some d1
             | (None, Some d2) -> Some d2
             | (Some d1, Some d2) ->
                let _ = if not (check_equal_field_term
                                  loc (fctx @ base_fctx) d1 d2) then
                          raise loc (FieldMismatch (f, true)) else ()
                in
                Some d1
             | (None, None) -> None)
          in
          { felem_id = f; felem_type = elem1.felem_type;
            felem_ptype = elem1.felem_ptype; felem_defn = defn_opt }
       | (None, None) ->
          (* This should never happen! *)
          raise dummy_loc (Failure "merge_fctxs")
     in
     new_elem :: fctx)
    sorted_names_and_deps []


(* The types (if flag = false) or the definitions (if flag = true) of two
   fields, which are mapped to the same field by a substitution, are unequal *)
exception FieldOverlapMismatch of Id.t * Id.t * bool

(* Apply a substitution to an fctx element *)
let subst_fctx_elem loc fctx (subst:field_subst) elem =
  let (new_id, defn_opt) = subst_id subst elem.felem_id in
  let new_defn_opt =
    match (elem.felem_defn, defn_opt) with
    | (None, _) -> defn_opt
    | (Some defn, None) -> Some (subst_field_term subst defn)
    | (Some defn, Some defn') ->
       if check_equal_field_term loc fctx (subst_field_term subst defn) defn'
       then (Some defn')
       else raise loc (FieldAlreadyDefined elem.felem_id)
  in
  { felem_id = new_id;
    felem_type = subst_field_term subst elem.felem_type;
    felem_ptype =
      (match elem.felem_ptype with
       | Some tp -> Some (subst_field_term subst tp)
       | None -> None);
    felem_defn = new_defn_opt }

(* Apply an fctx substitution to an fctx, raising a FieldOverlapMismatch if two
fields with distinct types or definitions are mapped to the same field *)
(* FIXME HERE: handle the fact that defns could require topo sorting... *)
(* FIXME HERE: make sure the subst domain includes the whole input context... *)
(* FIXME HERE: move these helper functions into the fctx section *)
let subst_fctx loc (subst:field_subst) (fctx:fctx) : fctx =
  (* For each fctx element elem satisfying pred, find the first element elem'
     which comes logically earlier in fctx (which means stored later in the list
     elems, because fctxs are stored backwards) that is mapped to the same field
     name by subst and also satisfies pred, if any. *)
  let rec mk_overlap_alist pred elems =
    match elems with
    | [] -> []
    | elem :: elems' ->
      if pred elem then
        (try (elem.felem_id,
              (List.find (fun elem' ->
                          pred elem' &&
                          Id.equal (fst (subst_id subst elem.felem_id))
                                   (fst (subst_id subst elem'.felem_id)))
                         elems').felem_id) :: mk_overlap_alist pred elems'
         with
           | Not_found -> mk_overlap_alist pred elems')
      else mk_overlap_alist pred elems'
  in
  (* Build overlap lists for error reporting, so that, if a type or definition
  mismatch occurs, we can say which two ops in the original fctx conflict. *)
  let tp_overlap_alist = mk_overlap_alist (fun _ -> true) fctx in
  let defn_overlap_alist = mk_overlap_alist (fun elem -> elem.felem_defn <> None) fctx in
  let overlap_lookup is_defn id_from =
    snd (List.find (fun p -> Id.equal id_from (fst p))
                   (if is_defn then defn_overlap_alist
                    else tp_overlap_alist))
  in
  let raise_overlap_error id_from is_defn =
         raise loc (FieldOverlapMismatch
                      (id_from, overlap_lookup is_defn id_from, is_defn))
  in
  (* Helper function to add a definition to an fctx elem *)
  let add_fctx_elem_defn fctx elem id_from id_to defn =
    match elem.felem_defn with
    | None -> { elem with felem_defn = Some defn }
    | Some defn' ->
       if check_equal_field_term loc fctx defn defn' then elem else
         raise_overlap_error id_from true
  in
  (* Helper function to add a definition to an fctx *)
  let rec add_fctx_defn fctx id_from id_to defn =
    match fctx with
    | [] -> raise loc (Failure "subst_fctx") (* Should not happen! *)
    | elem :: fctx' ->
      if Id.equal elem.felem_id id_to then
        add_fctx_elem_defn fctx' elem id_from id_to defn :: fctx'
      else
        elem :: add_fctx_defn fctx' id_from id_to defn
  in
  (* Now build up the out fctx, using the overlap lists to report any errors *)
  List.fold_right
    (fun elem fctx_out ->
     let elem_out = subst_fctx_elem loc fctx_out subst elem in
     match fctx_lookup fctx_out elem_out.felem_id with
     | None -> elem_out :: fctx_out
     | Some elem' ->
        let _ =
          if check_equal_field_term loc fctx_out elem.felem_type elem'.felem_type
          then ()
          else raise_overlap_error elem.felem_id false
        in
        (match elem.felem_defn with
         | None -> fctx_out
         | Some defn ->
            add_fctx_defn fctx_out elem.felem_id elem_out.felem_id defn)
    ) fctx []


(***
 *** The internal representation of specs
 ***)

(* A spec is represented internally as having two field contexts, one for ops
   and types (called just the "op context") and one for axioms and theorems
   (called the "axiom context"). The latter can depend on the former, but not
   vice-versa. *)
type spec = {
  spec_op_ctx : fctx;
  spec_axiom_ctx : fctx;
  spec_axiom_class_id : Id.t option;
  spec_axiom_class : field_term option (* FIXME HERE: document this above! *)
}

(* The empty local_spec *)
let empty_named_spec spec_id =
  { spec_op_ctx = []; spec_axiom_ctx = [];
    spec_axiom_class_id = Some spec_id; spec_axiom_class = None }

(* The number of fields in a spec (mostly for debugging purposes) *)
(* FIXME: remove this *)
let spec_length spec =
  List.length (spec.spec_op_ctx @ spec.spec_axiom_ctx)

(* Get the full fctx of a spec, including the axiom and op contexts. Remember
that fctxs are stored backwards, so the axiom context, which depends on the op
context, is listed first. *)
let spec_full_fctx spec = spec.spec_axiom_ctx @ spec.spec_op_ctx

(* Remove the axiom context of a spec *)
let remove_all_spec_axioms spec =
  { spec with spec_axiom_ctx = [] }

(* Remove some axioms from a spec *)
let remove_spec_axioms axioms spec =
  { spec with spec_axiom_ctx =
                List.filter (fun elem ->
                             not (List.exists (Id.equal elem.felem_id) axioms))
                            spec.spec_axiom_ctx }

(* Get the ids of all the ops *)
let spec_op_ids spec =
  List.rev_map (fun elem -> elem.felem_id) spec.spec_op_ctx

(* Get the ids of all the non-defined axioms *)
let spec_axiom_ids spec =
  List.rev
    (filter_map (fun elem -> if fctx_elem_has_def elem then None
                             else Some elem.felem_id)
                spec.spec_axiom_ctx)

(* Two specs were merged where the given field is an op in one spec and an axiom
in the other *)
exception OpAxiomMismatch of Id.t

(* Merge two specs by merging their op and axiom contexts *)
let merge_specs loc spec1 spec2 =
  (* Check for overlap between op and axiom contexts *)
  let _ = fctx_iter_shared_fields
            (fun id -> raise loc (OpAxiomMismatch id))
            spec1.spec_op_ctx spec2.spec_axiom_ctx in
  let _ = fctx_iter_shared_fields
            (fun id -> raise loc (OpAxiomMismatch id))
            spec2.spec_op_ctx spec1.spec_axiom_ctx in
  let op_ctx = merge_fctxs loc empty_fctx spec1.spec_op_ctx spec2.spec_op_ctx in
  let axiom_ctx =
    merge_fctxs loc op_ctx spec1.spec_axiom_ctx spec2.spec_axiom_ctx
  in
  {spec_op_ctx = op_ctx; spec_axiom_ctx = axiom_ctx;
   spec_axiom_class_id = None; spec_axiom_class = None}

(* A substitution into a spec would map an op and an axiom to the same name *)
exception OpAxiomOverlap of Id.t * Id.t

(* Apply a substitution to a spec *)
let subst_spec loc subst spec =
  let spec_ret = {spec_op_ctx = subst_fctx loc subst spec.spec_op_ctx;
                  spec_axiom_ctx = subst_fctx loc subst spec.spec_axiom_ctx;
                  spec_axiom_class_id = None; spec_axiom_class = None} in
  (* Check for overlap between op and axiom contexts in output spec *)
  let _ = fctx_iter_shared_fields
            (fun id ->
             let op_elem =
               List.find (fun elem ->
                          Id.equal (fst (subst_id subst elem.felem_id)) id)
                         spec.spec_op_ctx in
             let axiom_elem =
               List.find (fun elem ->
                          Id.equal (fst (subst_id subst elem.felem_id)) id)
                         spec.spec_axiom_ctx in
             raise loc (OpAxiomOverlap (op_elem.felem_id, axiom_elem.felem_id)))
            spec_ret.spec_op_ctx spec_ret.spec_axiom_ctx in
  spec_ret


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
 *** Name Translations
 ***)

(* A name translation specifies a field substitution, but can only be
   resolved into a concrete field substitution by giving it a set of
   field names to map *)
type name_translation_elem =
  (* Map a single name to another *)
  | NameXSingle of Id.t * Id.t
  (* Map all names with a given prefix to instead use a different prefix *)
  | NameXPrefix of string * string

type name_translation = name_translation_elem list

(* Map an identifier using a name translation *)
let rec translate_id xlate id =
  match xlate with
  | [] -> None
  | NameXSingle (id_from, id_to) :: xlate' ->
     if Id.equal id_from id then Some id_to else
       translate_id xlate' id
  | NameXPrefix (pre_from, pre_to) :: xlate' ->
     (match match_prefix id pre_from with
      | Some id_suffix ->
         Some (Id.of_string (pre_to ^ id_suffix))
      | None -> translate_id xlate' id)

(* Resolve a name translation into a name substitution for a spec; if
   the total flag is set, make the returned substitution be total on
   all fields of spec (even if it is the identity on some of them) *)
let resolve_name_translation ?(total=false) ?(ops_only=false) spec xlate =
  let op_subst =
    concat_map (fun elem ->
                let id = elem.felem_id in
                let mapped_id =
                  match translate_id xlate id with
                  | None -> if total then Some id else None
                  | Some id' -> Some id'
                in
                match mapped_id with
                | Some id' ->
                   (*
                 let _ = debug_printf "resolve_name_translation: mapped field %s to %s\n"
                                        (Id.to_string id) (Id.to_string id') in
                    *)
                   [(id, id', None)]
                | None -> [])
               spec.spec_op_ctx
  in
  if ops_only then op_subst else
    op_subst
    @ filter_map (fun elem ->
                  let id = elem.felem_id in
                  match translate_id xlate id with
                  | Some id' ->
                     (* Filter out mappings on "__eq" axioms *)
                     if has_suffix id "__eq" then None else
                       Some (id, id', None)
                  | None -> None)
                 spec.spec_axiom_ctx


(***
 *** Potential Morphisms
 ***)

(* A potential morphism is intuitively a morphism that does not yet have a
target spec. It thus also does not have any typeclass instances defined yet, and
so contains just a source spec (referred to by name) and a substitution. *)
type potential_morphism = spec_globref * spec * field_subst

(* Build the identity potential morphism *)
let make_id_pot_morphism spec spec_globref : potential_morphism =
  (spec_globref, spec,
   mk_id_subst (List.map (fun elem -> elem.felem_id)
                         (spec_full_fctx spec)))

(* Substitute into a potential morphism *)
let subst_potential_morphism subst pot_m =
  let (globref, spec, subst') = pot_m in
  (globref, spec, compose_substs subst subst')

(* Fresh names for generating instance names *)
let inst_name_counter = ref 0
let get_fresh_inst_name id =
  let i = !inst_name_counter in
  let _ = inst_name_counter := i + 1 in
  Id.of_string (Id.to_string id ^ "__inst__" ^ string_of_int i)

(* Add an instance of the axiom typeclass of the domain of a pot morphism *)
let add_potential_morphism_instance loc fctx (pot_m : potential_morphism) =
  let (globref, spec, subst) = pot_m in
  let (axiom_class_id, axiom_class) =
    match (spec.spec_axiom_class_id, spec.spec_axiom_class) with
    | (Some id, Some tp) -> (id, tp)
    | _ -> raise loc (Failure "add_potential_morphism_instances")
  in
  let axiom_ids = spec_axiom_ids spec in
  let inst_id = get_fresh_inst_name axiom_class_id in
  add_record_instance
    (loc, Name inst_id)
    (fctx_params loc fctx)
    (field_term_to_expr ~field_params:true
                        (subst_field_term subst axiom_class))
    (List.map (fun ax_id ->
               let (ax_to_id, ax_defn_opt) = subst_id subst ax_id in
               (field_axelem_id ax_id,
                match ax_defn_opt with
                | Some pf_d ->
                   field_term_to_expr ~field_params:true pf_d
                | None -> mk_var (loc, ax_to_id)))
              axiom_ids)


(***
 *** Spec Morphisms
 ***)

(* A morphism is intuitively a substitution that maps from a source spec to a
target spec. Associated with this mapping is a set of typeclass instances, in
the context of the co-domain / target spec, of all of the typeclasses associated
with the domain / source spec; these include one instance for every op in the
source spec, and a single instance for all the axioms in the source spec. *)
type morphism = {
  morph_source : spec; (* FIXME: remove source and target specs in favor of refs *)
  morph_source_ref : spec_globref;
  morph_target : spec;
  morph_target_ref : spec_globref;
  morph_subst : field_subst;
  morph_instance : constant
}

(* Global table of named morphisms, indexed by the axiom typeclass instance *)
let morphism_table = ref (Cmap.empty)

(* Register a morphism in the morphism table *)
let register_morphism morph =
  morphism_table := Cmap.add morph.morph_instance morph !morphism_table

(* Indicates that a morphism was not found *)
exception MorphismNotFound of qualid

(* Indicates that a field is not in the target of a morphism *)
exception FieldNotInMoprphTarget of Id.t

(* Indicates that a field is no longer defined in the target of a morphism *)
exception FieldNotDefinedInMoprphTarget of Id.t

(* Look up a morphism by reference, raising Not_found if it does not exist *)
let lookup_morphism r =
  let loc = loc_of_reference r in
  let qualid = located_elem (qualid_of_reference r) in
  try
    let c = lookup_constant loc qualid in
    Cmap.find c !morphism_table
  with Not_found ->
    raise loc (MorphismNotFound qualid)

(* Apply a morphism to a spec. This is accomplished by: merging the spec with
the source of the morphism, which checks that all the types and definitions in
the spec agree with the morphism; removing any axioms listed in the domain spec;
applying the substitution of the morphism; and then merging the target spec with
the result, to add the axioms of the target spec as well as any additional ops
not in the range of the substitution. *)
let apply_morphism loc morph spec =
  let spec1 = merge_specs loc spec morph.morph_source in
  let spec2 = remove_spec_axioms (spec_axiom_ids morph.morph_source) spec1 in
  let spec3 = subst_spec loc morph.morph_subst spec2 in
  merge_specs loc spec3 morph.morph_target


(* Define a named morphism from the from spec to the to spec, both
   given by reference, via the given name translation *)
let start_morphism morph_name from_ref to_ref xlate =
  let loc = located_loc morph_name in
  let from_locref = located_elem (qualid_of_reference from_ref) in
  let to_locref = located_elem (qualid_of_reference to_ref) in
  let (from_spec, from_gref) = lookup_spec_and_globref from_locref in
  let (to_spec, to_gref) = lookup_spec_and_globref to_locref in
  let subst_nodefs = resolve_name_translation ~ops_only:true ~total:true
                                              from_spec xlate in
  let subst_ops =
    List.map (fun (id_from, id_to, _) ->
              match (fctx_lookup from_spec.spec_op_ctx id_from,
                     fctx_lookup to_spec.spec_op_ctx id_to) with
              | (Some from_elem, Some to_elem) ->
                 if not (fctx_elem_has_def from_elem) then
                   (id_from, id_to, to_elem.felem_defn)
                 else if not (fctx_elem_has_def to_elem) then
                   raise loc (FieldNotDefinedInMoprphTarget id_to)
                 else
                   (id_from, id_to, None)
              | (Some _, None) ->
                 raise loc (FieldNotInMoprphTarget id_to)
              | _ -> raise loc (Failure ("start_morphism: could not find id "
                                         ^ Id.to_string id_from
                                         ^ " in source spec")))
             subst_nodefs
  in
  let _ =
    (* Check that subst_ops on the from_spec ops is compatible with to_spec *)
    merge_specs loc (subst_spec loc subst_ops
                                (remove_all_spec_axioms from_spec))
                to_spec
  in
  let finish_hook gr =
    register_morphism
      { morph_source = from_spec;
        morph_source_ref = from_gref;
        morph_target = to_spec;
        morph_target_ref = to_gref;
        morph_subst =
          (* Build a substitution that maps all the axioms of from_spec to
          applications of the morphism instance *)
          (let op_ids = spec_op_ids to_spec in
           subst_ops @
             (make_subst_for_defs
                (List.map
                   (fun ax_id ->
                    (ax_id,
                     mk_field_term
                       op_ids
                       (CAppExpl
                          (loc,
                           (None,
                            Qualid (loc, qualid_cons from_locref
                                                     (field_axelem_id ax_id)),
                            None),
                           List.map (fun id ->
                                     mk_var (loc, fst (subst_id subst_ops id)))
                                    (spec_op_ids from_spec)
                           @ [mk_global_app_named_args
                                gr
                                (List.map
                                   (fun op_id ->
                                    (field_param_id op_id,
                                     mk_var (loc, op_id)))
                                   op_ids)]
                       ))
                   ))
                   (spec_axiom_ids from_spec))));
          morph_instance = match gr with
                           | ConstRef c -> c
                           | _ -> anomaly (str "Morphism not a constant") }
  in
  begin_instance
    ~hook:finish_hook
    (fctx_params loc to_spec.spec_op_ctx @
       [mk_implicit_assum morph_spec_arg_id
                          (mk_ref_app_named_args
                             loc
                             (spec_typeclass_ref loc to_locref) [])])
    (lname_of_lident morph_name)
    (mk_ref_app_named_args
       loc (spec_typeclass_ref loc from_locref)
       (* FIXME HERE: make this map into an operation on substs or fctxs *)
       (rev_filter_map
          (fun elem ->
           if fctx_elem_has_def elem then None else
             Some (field_param_id elem.felem_id,
                   let (to_id,defn_opt) = subst_id subst_ops elem.felem_id in
                   match defn_opt with
                   | Some _ -> mkRefC (Qualid (loc, qualid_cons to_locref to_id))
                   | None -> mk_var (loc, field_param_id to_id)))
          from_spec.spec_op_ctx))


(***
 *** Building up the current spec
 ***)

(* The currrent spec being defined, if one exists, along with its module path *)
let current_spec : (DirPath.t * spec) option ref = ref None

(* There is no current spec *)
exception NoCurrentSpec

(* There is already a current spec *)
exception IsCurrentSpec

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Check that all the ops and axioms of the current spec still exist *)
let check_current_spec spec_path spec =
  { spec with
    spec_op_ctx =
      List.filter (fun elem ->
                   Nametab.exists_cci (make_path spec_path elem.felem_id))
                  spec.spec_op_ctx;
    spec_axiom_ctx =
      List.filter (fun elem ->
                   Nametab.exists_cci (make_path spec_path elem.felem_id))
                  spec.spec_axiom_ctx }

(* Get the current spec or throw an exception, making sure we are still in the
correct module for the spec *)
let get_current_spec_opt loc =
  match !current_spec with
  | Some (spec_path, spec) ->
     if DirPath.equal spec_path (Lib.cwd_except_section ()) then
       let new_spec = check_current_spec spec_path spec in
       let _ = current_spec := Some (spec_path, new_spec) in
       Some (spec_path, new_spec)
     else if Nametab.exists_dir spec_path then
       raise loc (Failure "get_current_spec")
     else
       (* If the module for the current spec no longer exists, it was
          probably removed by an Undo, so reset to no current spec *)
       let _ = current_spec := None in None
  | None -> raise loc NoCurrentSpec

let get_current_spec loc =
  match get_current_spec_opt loc with
  | Some (_, spec) -> spec
  | None -> raise loc NoCurrentSpec

(* Update the current spec, if it exists, by applying f *)
let update_current_spec loc f =
  match get_current_spec_opt loc with
  | Some (spec_path, spec) ->
     current_spec := Some (spec_path, f spec)
  | None -> raise loc NoCurrentSpec

(* The op_ctx of the current spec *)
let current_op_ctx loc =
  (get_current_spec loc).spec_op_ctx

(* The op_ctx and the axiom ctx of the current spec *)
let current_full_ctx loc =
  spec_full_fctx (get_current_spec loc)

(* The op parameters in the current spec *)
let current_op_params loc =
  fctx_params loc (current_op_ctx loc)

(* All the parameters in the current spec *)
let current_all_params loc =
  fctx_params loc (current_full_ctx loc)

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to the current spec, creating a type-class for it *)
let add_declared_op op_name op_type =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let _ = debug_printf 2 "\nadd_declared_op: %s of type %a in context %s\n"
                       (Id.to_string op_id) pp_constr_expr op_type
                       (fctx_to_string (current_op_ctx loc))
  in

  (* Add a type-class op_name__class : Type := op_name : op_type *)
  let (tp_defn, cls_defn) =
    add_local_op_typeclass loc (current_op_ctx loc)
                           (field_class_id op_id) op_id false op_type
  in

  update_current_spec
    loc
    (fun s ->
     { s with
       spec_op_ctx =
         fctx_cons op_id tp_defn (Some cls_defn) None s.spec_op_ctx })

(* Add an axiom to the current spec, creating a definition for its type *)
let add_axiom ax_name ax_type =
  let ax_id = located_elem ax_name in
  let loc = located_loc ax_name in
  let _ = debug_printf 2 "\nadd_axiom: %s\n" (Id.to_string ax_id) in
  (* Add a type-class ax_name__class : Prop := ax_name : ax_type *)
  let (tp_defn, cls_defn) =
    add_local_op_typeclass loc (current_op_ctx loc)
                           (field_class_id ax_id) ax_id true ax_type
  in
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axiom_ctx = fctx_cons ax_id tp_defn (Some cls_defn) None s.spec_axiom_ctx })

(* Add a defined op to the current spec, creating a type-class and def for it *)
let add_defined_op op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  (*
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
   *)
  let op_ctx = current_op_ctx loc in
  (* let op_var_id = add_suffix_l op_name "var" in *)
  let _ = debug_printf 2 "\nadd_defined_op: %s\n" (Id.to_string op_id) in

  (* Add a type-class for op_name__class : Type := op_name__var : EqObj op_body *)
  (*
  let (tp_defn, cls_defn) =
    add_local_op_typeclass loc op_ctx op_id (field_class_id op_id) false op_type in
   *)

  (* Add a definition op_name : op_type := op_body *)
  let (tp_defn, def_defn) =
    add_local_definition loc op_ctx op_id op_type_opt op_body in

  (* Add the new op to spec *)
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_op_ctx =
         fctx_cons op_id tp_defn None (Some def_defn) s.spec_op_ctx })

(* FIXME HERE: make sure this is right: use typeclasses? *)
let add_defined_theorem thm_name thm_type thm_body =
  raise dummy_loc (Failure "add_defined_theorem: not implemented (FIXME HERE)")
  (*
  let thm_id = located_elem thm_name in
  let loc = located_loc thm_name in
  let (tp_defn, cls_defn) =
    add_local_op_typeclass loc (current_op_ctx loc) thm_id true thm_type
  in
  let def_defn =
    add_local_definition loc (current_full_ctx loc) thm_id
                         (Some (mk_var (loc, field_type_id thm_id))) thm_body
  in
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axiom_ctx = fctx_cons thm_id tp_defn cls_defn
                                  (Some def_defn) s.spec_axiom_ctx })
   *)

(* Complete the current spec, by creating its axiom type-class and
   registering it in the global spec table. No more axioms can be
   added to a spec once it has been completed. Return the globalized
   version of the current spec. *)
let complete_spec loc =
  match !current_spec with
  | None -> raise loc NoCurrentSpec
  | Some (_, spec) ->
     let class_id = match spec.spec_axiom_class_id with
       | Some id -> id
       | None -> raise loc (Failure "complete_spec")
     in
     let ax_fields =
       List.rev_map
         (fun elem -> ((loc, field_axelem_id elem.felem_id),
                       mk_var (loc, field_class_id elem.felem_id),
                       true))
         (List.filter (fun elem -> elem.felem_defn = None) spec.spec_axiom_ctx)
     in
     let ax_cls =
       add_local_record_typeclass loc (current_op_ctx loc)
                                  class_id true ax_fields in
     let spec_globref = global_modpath (Nametab.locate (qualid_of_ident class_id)) in
     let _ =
       register_spec spec_globref {spec with spec_axiom_class = Some ax_cls}
     in
     spec

(* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  if !current_spec = None then
    let _ = begin_module spec_lid in
    let cur_path = Lib.cwd_except_section () in
    current_spec := Some (cur_path, empty_named_spec (located_elem spec_lid))
  else
    raise (located_loc spec_lid) IsCurrentSpec

(* Finish the interactive definition of a new spec by completing it
   and clearing current_spec; return the newly defined spec *)
let end_new_spec lid =
  let loc = located_loc lid in
  match !current_spec with
  | Some (spec_path, spec) ->
     let class_id = match spec.spec_axiom_class_id with
       | Some id -> id
       | None -> raise loc (Failure "complete_spec")
     in
     if Id.equal class_id (located_elem lid) then
       let spec = complete_spec loc in
       let _ = end_module lid in
       let _ = current_spec := None in
       spec
     else
       raise loc WrongCurrentSpecName
  | None -> raise loc NoCurrentSpec

(* Build a new spec in a new module called spec_id, calling builder
   inside that new module to build the spec. Builder should not
   complete or globalize the spec. Unlike begin_new_spec,
   within_named_spec can be nested inside another spec definition *)
let within_named_spec spec_lid builder =
  raise (located_loc spec_lid) (Failure "within_named_spec (FIXME HERE NOW)")
  (*
  let spec_id = located_elem spec_lid in
  let loc = located_loc spec_lid in
  let saved_spec = !current_spec in
  let _ = current_spec := Some (empty_named_spec spec_id) in
  let spec = within_module spec_lid
                           (fun () -> builder (); complete_spec loc) in
  let _ = current_spec := saved_spec in
  spec
   *)


(***
 *** Spec Terms and Imports
 ***)

(* Spec terms are syntactic forms for building specs from existing
   specs *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * Loc.t * name_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * reference
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs of spec_term * Loc.t * (lident * Constrexpr.constr_expr) list

(* Interpret a spec term into a spec plus a list of potential morphisms to the
returned spec. The spec term is not allowed to add definitions. *)
let rec interp_spec_term sterm : spec * potential_morphism list =
  match sterm with
  | SpecRef r ->
     (try
         let locref = spec_locref_of_ref r in
         let (spec, globref) = lookup_spec_and_globref locref in
         (spec, [make_id_pot_morphism spec globref])
       with Not_found ->
         user_err_loc (loc_of_reference r, "_",
                       str ("No spec named " ^ string_of_reference r)))
  | SpecXlate (sterm', loc, xlate) ->
     let (spec, insts) = interp_spec_term sterm' in
     let subst = resolve_name_translation spec xlate in
     (*
     let _ =
       List.iter (fun (id_from, id_to) ->
                   debug_printf "Translating %s to %s\n"
                                  (Id.to_string id_from)
                                  (Id.to_string id_to)) subst in
      *)
     (subst_spec loc subst spec,
      List.map (subst_potential_morphism subst) insts)
  | SpecSubst (sterm', morph_ref) ->
     (try
         let (spec, insts) = interp_spec_term sterm' in
         let loc = loc_of_reference morph_ref in
         let morph = lookup_morphism morph_ref in
         (apply_morphism loc morph spec,
          make_id_pot_morphism morph.morph_target morph.morph_target_ref ::
            List.map (subst_potential_morphism morph.morph_subst) insts)
       with Not_found ->
         user_err_loc (loc_of_reference morph_ref, "_",
                       str ("No morphism named " ^ string_of_reference morph_ref)))
  | SpecAddDefs (sterm', loc, defs) ->
     let (spec, insts) = interp_spec_term sterm' in
     let subst =
       (* FIXME HERE: filter the free variables of each definition *)
       make_subst_for_defs (List.map (fun ((_, id), d) ->
                                      (id, mk_fctx_term spec.spec_op_ctx d))
                                     defs)
     in
     (subst_spec loc subst spec,
      List.map (subst_potential_morphism subst) insts)

(* Add an fctx_elem to the current spec *)
let import_fctx_elem loc is_axiom elem =
  match (is_axiom, elem.felem_defn) with
  | (true, None) ->
     add_axiom (loc, elem.felem_id) (field_term_to_expr elem.felem_type)
  | (true, Some defn) ->
     add_defined_theorem (loc, elem.felem_id)
                         (field_term_to_expr elem.felem_type)
                         (field_term_to_expr defn)
  | (false, None) ->
     add_declared_op (loc, elem.felem_id) (field_term_to_expr elem.felem_type)
  | (false, Some defn) ->
     add_defined_op (loc, elem.felem_id)
                    (Some (field_term_to_expr elem.felem_type))
                    (field_term_to_expr defn)

(* Import a spec term into the current spec *)
let import_spec_term loc sterm =
  let (spec, insts) = interp_spec_term sterm in
  (* Do merge_specs to test for errors so import_fctx_elem doesn't have to *)
  let _ = merge_specs loc spec (get_current_spec loc) in
  let _ =
    List.iter (import_fctx_elem loc false) (List.rev spec.spec_op_ctx)
  in
  let _ =
    List.iter (import_fctx_elem loc true) (List.rev spec.spec_axiom_ctx)
  in
  List.iter (add_potential_morphism_instance loc (current_full_ctx loc)) insts


(***
 *** Additions to the Coq parser
 ***)

(* Run f, catching any exceptions and turning them into user_errors *)
(* FIXME: actually write this! *)
let reporting_exceptions f =
  f ()

(* FIXME: get the locations of all the identifiers right! *)

(* Syntactic class to parse name translation elements *)
VERNAC ARGUMENT EXTEND name_translation_elem
  | [ ident(lhs) "+->" ident(rhs) ] -> [ NameXSingle (lhs,rhs) ]
  | [ ident(lhs) "%" "+->" ident(rhs) "%" ] ->
     [ NameXPrefix (Id.to_string lhs, Id.to_string rhs) ]
END

(* Syntactic class to parse name translations *)
VERNAC ARGUMENT EXTEND name_translation
  | [ name_translation_elem(elem) ";" name_translation (rest) ] -> [ elem::rest ]
  | [ name_translation_elem(elem) ] -> [ [elem] ]
END

(* Syntactic class to parse spec term defs *)
type spec_term_defs = (lident * Constrexpr.constr_expr) list
VERNAC ARGUMENT EXTEND spec_term_defs
  | [ ident(id) ":=" constr(def) ";" spec_term_defs(rest) ] -> [ ((dummy_loc,id), def)::rest ]
  | [ ident(id) ":=" constr(def) ] -> [ [(dummy_loc,id), def] ]
END

(* Syntactic class to parse spec terms *)
VERNAC ARGUMENT EXTEND spec_term
  | [ global(r) ] -> [ SpecRef r ]
  | [ spec_term(st) "{" name_translation(xlate) "}" ] -> [ SpecXlate (st, dummy_loc, xlate) ]
  | [ spec_term(st) "[" global(morph_ref) "]" ] -> [ SpecSubst (st, morph_ref) ]
  | [ spec_term(st) "with" spec_term_defs(defs) ] -> [ SpecAddDefs (st, dummy_loc, defs) ]
END

(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec
  (* Define a spec via a spec term *)
  | [ "Spec" ident(spec_name) ":=" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            ignore
              (within_named_spec (dummy_loc, spec_name)
                                 (fun () -> import_spec_term dummy_loc st))) ]

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
           (fun () -> add_declared_op (dummy_loc,id) tp) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" ident(id) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) (Some tp) body) ]
  (* Add a defined op without a type *)
  | [ "Spec" "Definition" ident(id) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) None body) ]

  (* Add an axiom *)
  | [ "Spec" "Axiom" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_axiom (dummy_loc,id) tp) ]

  (* Import a spec term *)
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term dummy_loc st) ]
END

(* Top-level syntax for morphisms *)
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
