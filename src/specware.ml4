
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
open Misctypes
open Decl_kinds


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

(* Map f on a list and concatenate the results *)
let concat_map f l =
  List.concat (List.map f l)

(* Topo sort failed because of a circularity *)
exception TopoCircularity of int

(* Stable reverse topological sort: sort l so that every element x
   comes before its dependencies, favoring the existing ordering of l
   where possible. The dependencies of x are all nodes y whose key,
   given by the key function, is key_eq to a key in (deps x). *)
let rec stable_reverse_topo_sort loc key key_eq deps l =
  let arr = Array.of_list l in
  let arr_deps = Array.make (List.length l) [] in
  let visited = Array.make (List.length l) false in
  let rec get_node_by_key_help k j =
    if j > Array.length arr then None
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
             if List.mem j arr_deps.(i) then 1
             else if List.mem i arr_deps.(j) then -1
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

(* Build an expression for a local reference applied to named implicit
   args, where the args are given as (name,value) pairs *)
let mk_ref_app_named_args r args =
  CApp (dummy_loc,
        (None, CRef (r, None)),
        List.map (fun (id,arg) ->
                  (arg, Some (dummy_loc, ExplByName id))) args)

(* Build an expression for a variable applied to named implicit args,
   where the args are given as (name,value) pairs *)
let mk_id_app_named_args id args =
  mk_ref_app_named_args (Ident id) args

(* Build a qualified id (NOTE: dir is *not* reversed here) *)
let mk_qualid dir id =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) id

(* Cons an id onto the end of a qualid *)
let qualid_cons qualid id =
  let (mod_path,mod_name) = repr_qualid qualid in
  make_qualid (DirPath.make (DirPath.repr mod_path @ [mod_name])) id

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
  mk_ref_app_named_args (Qualid (dummy_loc, qualid_of_global gr)) args

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
  interp
    (located_loc id,
     VernacDefinition
       ((None, Definition), id,
        DefineBody (params, None, body, type_opt)))

(* Add a type-class to the current Coq image, where is_op_class says
   whether to add an operational type-class in Type (if true) or a
   normal type-class in Prop (if false), and fields is a list of
   triples (id, type, coercion_p) to be passed to mk_record_field *)
let add_typeclass class_id is_op_class params fields =
  interp
    (located_loc class_id,
     VernacInductive (false, BiFinite,
                      [((false, class_id), params,
                        Some (if is_op_class then type_expr else prop_expr),
                        Class is_op_class,
                        if is_op_class then
                          match fields with
                          | [] -> Constructors []
                          | [(id, tp, _)] ->
                             Constructors [false, (id, tp)]
                          | _ -> raise (located_loc class_id) (Failure "add_typeclass")
                        else
                          RecordDecl (None, List.map mk_record_field fields)),
                       []]))

(* Add an instance using a single term *)
let add_term_instance inst_name inst_params inst_tp inst_body =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, inst_params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  Some (false, inst_body),
                  None))


(* Add an instance using the given record fields *)
let add_record_instance inst_name inst_params inst_tp inst_fields =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, inst_params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  Some (true,
                        CRecord (loc, None,
                                 List.map (fun (id,tp) -> (Ident (loc, id),tp))
                                          inst_fields)),
                  None))

(* Begin an interactively-defined instance *)
let begin_instance inst_name inst_params inst_tp =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, inst_params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  None, None))

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
(* FIXME HERE: make sure this works! *)
let check_equal_term params t1 t2 =
  try
    interp
      (dummy_loc,
       VernacCheckMayEval
         (None, None,
          (Constrexpr_ops.mkCProdN
             dummy_loc
             params
             (CCast (dummy_loc,
                     CApp (dummy_loc,
                           (None, mk_reference ["Coq"; "Init"; "Logic"]
                                               (Id.of_string "eq_refl")),
                           [(t1, None)]),
                     CastConv (mk_equality t1 t2))))));
    true
  with UserError _ -> false

(* Unfold the given global references (which must all be constants) and then
   fold the given terms, all relative to the given parameters *)
let unfold_fold_term params unfolds folds t =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let impls, ((env_bl, ctx), imps1) =
    Constrintern.interp_context_evars env evdref params in
  (* FIXME: check that evdref is empty...? (Maybe done by interp_constr?) *)
  let unfold_redfun =
    Tacred.unfoldn
      (List.map (fun gr ->
                 match gr with
                 | ConstRef c -> (Locus.AllOccurrences, EvalConstRef c)
                 | _ -> raise dummy_loc (Failure "unfold_fold_term"))
                unfolds) in
  let fold_redfun =
    Tacred.fold_commands
      (List.map (fun t -> fst (Constrintern.interp_constr env_bl !evdref t)) folds) in
  let constr_out =
    fold_redfun
      env_bl !evdref
      (unfold_redfun env_bl !evdref
                     (fst (Constrintern.interp_constr env_bl !evdref t))) in
  Constrextern.extern_constr true env_bl !evdref constr_out


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

(* Return a qualid that points to field fname in spec locref *)
let field_in_spec locref fname =
  qualid_cons locref fname

(* A global reference to a spec is a global reference to the spec's
   module *)
type spec_globref = module_path

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
let field_in_global_spec globref fname =
  field_in_spec (spec_globref_to_locref globref) fname


(***
 *** Field Substitutions
 ***)

(* A field substitution is a finite mapping on field names *)
type field_subst = (Id.t * Id.t) list

(* Make the identity substitution on the given fields *)
let mk_id_subst fields = List.map (fun id -> (id,id)) fields

(* Equality on field substitutions *)
(* FIXME: can the orders be different? *)
(* FIXME: is this needed? *)
let rec eq_subst s1 s2 =
  match (s1, s2) with
  | ([], []) -> true
  | ((id1, id1') :: s1', (id2, id2') :: s2') ->
     Id.equal id1 id2 && Id.equal id1' id2' && eq_subst s1' s2'
  | _ -> false

(* Apply a field substitution to a field *)
let rec subst_id subst id =
  match subst with
  | [] -> id
  | (id_from, id_to) :: subst' ->
     if Id.equal id_from id then id_to else subst_id subst' id

(* Apply field substitution subst to all the fields in the range of
   another field substitution subst2 *)
let rec subst_field_subst subst subst2 =
  match subst2 with
  | [] -> []
  | (id_from, id_to) :: subst2' ->
     (id_from, subst_id subst id_to)
     :: subst_field_subst subst subst2'

(* Build the identifier used to quantify over a field as a local
   variable *)
let field_var_id f = add_suffix f "param"

(* Get the identifier used locally for the type of a field *)
let field_type_id f = add_suffix f "type"

(* Get the identifier used locally for the type-class of a field *)
let field_class_id f = add_suffix f "class"

(* The name of the instance associated with a field *)
let field_inst_id f = add_suffix f "inst"

(* Get the range of subst, as a list of identifiers *)
let subst_range subst =
  List.map snd subst

(* Turn a name substitution into a list of (name,value) pairs, where
   value is a term expression; omit pairs where name = value *)
let subst_to_args subst =
  filter_map
    (fun (id_from, id_to) ->
     if Id.equal id_from id_to then None else
       Some (field_var_id id_from, mk_var (dummy_loc, id_to)))
    subst

(* Turn a name substitution into a list of pairs (name,inst), where
   inst is the instance of the class associated with the old name (the
   lhs) created from the new name (the rhs) *)
let subst_to_inst_args subst =
  List.map
    (fun (id_from, id_to) ->
     (field_var_id id_from, mk_var (dummy_loc, field_inst_id id_to)))
    subst

(* Get the global references associated with all the instances mapped to by a
   substitution; NOTE: this only works inside a spec in which the substitution
   is well-typed *)
let subst_inst_globs subst =
  List.map (fun (_, id_to) ->
            Nametab.locate (qualid_of_ident (field_inst_id id_to))) subst


(***
 *** Field Contexts
 ***)

(* FIXME: document this type! *)
type spec_defn =
  | Local_Defn of Id.t * Id.t list
  | Global_Defn of global_reference * global_reference list * field_subst
  | Term_Defn of constr_expr * Id.t list

(* A field context specifies a list of named fields, each of which has
   a type and an optional definition. Fields can also be marked as
   "ghost fields", meaning that they are actually derived from other
   fields (e.g., equality axioms being derived from defined fields).

   NOTE: field contexts are stored backwards, in that the "earlier"
   fields are stored later in the list; i.e., fields can only refer to
   fields later in a field context. This is to make it easy to add new
   fields as we go *)
type fctx_elem =
    { felem_id : Id.t;
      felem_is_ghost : bool;
      felem_type_defn : spec_defn;
      felem_def_defn : spec_defn option
    }
type fctx = fctx_elem list

(* Get the fields referenced by the args of a spec_defn *)
let spec_defn_deps d =
  match d with
  | Local_Defn (_, args) -> args
  | Global_Defn (_, _, args) -> List.map snd args
  | Term_Defn (_, args) -> args

(* Turn a definition into a term *)
let spec_defn_term d =
  match d with
  | Local_Defn (id, _) -> mk_var (dummy_loc, id)
  | Global_Defn (r, _, subst) ->
     mk_global_app_named_args r (subst_to_inst_args subst)
  | Term_Defn (t, _) -> t

(* Return true iff d is a global definition *)
let spec_defn_is_global d =
  match d with
  | Global_Defn (_, _, _) -> true
  | _ -> false

(* Get the id for the named parameter used for a field *)
let fctx_elem_var_id elem =
  field_var_id elem.felem_id

(* Return true iff an fctx_elem is defined *)
let fctx_elem_is_def elem =
  match elem.felem_def_defn with
  | Some _ -> true
  | None -> false

(* Return true iff the type of fctx_elem is a global *)
let fctx_elem_has_global_type elem =
  spec_defn_is_global elem.felem_type_defn

(* Return true iff the fctx_elem has a global definition *)
let fctx_elem_has_global_def elem =
  match elem.felem_def_defn with
  | Some d -> spec_defn_is_global d
  | None -> false

(* Build a term for the type of a field *)
let fctx_elem_type elem = spec_defn_term elem.felem_type_defn

(* Build a term for the definition of a field; this type depends on
   the fields in the fctx (see fctx_elem_type) *)
let fctx_elem_defn elem =
  match elem.felem_def_defn with
  | Some d -> spec_defn_term d
  | None -> raise dummy_loc (Failure "fctx_elem_defn")

(* Get the fields referenced by the args in an fctx_elem *)
let fctx_elem_deps elem =
  let deps_tp = spec_defn_deps elem.felem_type_defn in
  match elem.felem_def_defn with
  | Some d -> deps_tp @ spec_defn_deps d
  | None -> deps_tp

(* Add a definition to an undefined fctx elem *)
let fctx_elem_add_def elem d =
  match elem.felem_def_defn with
  | None -> { elem with felem_def_defn = Some d }
  | Some _ -> raise dummy_loc (Failure "fctx_elem_add_def")

(* Find a named field in an fctx, returning None if not found *)
let rec fctx_lookup fctx f =
  match fctx with
  | [] -> None
  | elem :: fctx' ->
     if Id.equal f elem.felem_id then
       Some elem
     else
       fctx_lookup fctx' f

(* Apply a name substitution to a definition *)
let subst_spec_defn subst d =
  match d with
  | Global_Defn (r, elims, args) ->
     Global_Defn (r, elims, subst_field_subst subst args)
  | _ -> raise dummy_loc (Failure "subst_spec_defn")

(* Apply a name substitution to an optional definition *)
let subst_spec_defn_opt subst d_opt =
  match d_opt with
  | Some d -> Some (subst_spec_defn subst d)
  | None -> None

(* Apply a name substitution to an fctx_elem *)
let subst_fctx_elem subst elem =
  { felem_id = subst_id subst elem.felem_id;
    felem_is_ghost = elem.felem_is_ghost;
    felem_type_defn = subst_spec_defn subst elem.felem_type_defn;
    felem_def_defn = subst_spec_defn_opt subst elem.felem_def_defn }

(* Apply a name substitution to an fctx *)
let subst_fctx subst fctx =
  List.map (subst_fctx_elem subst) fctx

(* Build the identity substitution for the fields in an fctx
   (remembering that field contexts are stored backwards) *)
let subst_from_fctx fctx =
  List.rev_map (fun elem -> (elem.felem_id, elem.felem_id)) fctx

(* Build a spec_defn from an id and the current fctx *)
let mk_local_spec_defn fctx id =
  Local_Defn (id, List.map (fun e -> e.felem_id) fctx)

(* Build a spec_defn from an id and a term *)
let mk_term_spec_defn fctx body =
  Term_Defn (body, List.map (fun e -> e.felem_id) fctx)

(* Subtract the fields of fctx2 from fctx1, returning both the
   remaining fields from fctx1 and also the list of fctx elems that
   are defined in fctx1 but not in fctx2 (intuitively, subtracting
   fctx2 removes these fields but maybe not their definitions...);
   also call check_fun with each pair of context elements from the two
   contexts that match *)
let rec fctx_subtract check_fun fctx1 fctx2 =
  let def_subs = ref [] in
  let ret_fctx =
    List.filter
      (fun elem1 ->
       not (List.exists
              (fun elem2 ->
               Id.equal elem1.felem_id elem2.felem_id &&
                 let _ = check_fun elem1 elem2 in
                 let _ = if fctx_elem_is_def elem1
                            && not (fctx_elem_is_def elem2) then
                           def_subs := elem1 :: !def_subs
                         else () in
                 true)
              fctx2))
      fctx1 in
  (ret_fctx, !def_subs)

(* Cons a field to a field context *)
let fctx_cons id is_ghost tp_defn def_defn_opt fctx =
  { felem_id = id; felem_is_ghost = is_ghost;
    felem_type_defn = tp_defn;
    felem_def_defn = def_defn_opt } :: fctx

(* Convert a single fctx_elem to an implicit class assumption *)
let fctx_elem_to_param fctx_elem =
  mk_implicit_assum (fctx_elem_var_id fctx_elem)
                    (fctx_elem_type fctx_elem)

(* Convert an fctx to a list of class parameters, one for each field
   in the context (remember: fctx is reversed) *)
let fctx_params fctx =
  List.rev_map fctx_elem_to_param fctx

(* Add a definition to the current module / spec, relative to the
   given fctx, and return a local spec_defn for the new definition *)
let add_local_definition id fctx type_opt body =
  let _ = add_definition id (fctx_params fctx) type_opt body in
  mk_local_spec_defn fctx (located_elem id)

(* Add a type class to the current module / spec, relative to the
   given fctx, and return a local spec_defn for the new definition *)
let add_local_typeclass id is_op_class fctx fields =
  let _ = add_typeclass id is_op_class (fctx_params fctx) fields in
  mk_local_spec_defn fctx (located_elem id)

(* Turn a definition into a term that is local to the current spec, by unfolding
   global definitions and the eliminators and instances they use *)
let spec_defn_term_local params d =
  match d with
  | Global_Defn (r, elims, subst) ->
     let inst_globs = subst_inst_globs subst in
     let field_terms =
       List.map (fun id ->
                 mk_id_app_named_args
                   (dummy_loc, id)
                   [(field_class_id id, mk_var (dummy_loc, field_var_id id))])
                (subst_range subst)
     (* [] *)
     in
     unfold_fold_term params (r::inst_globs @ elims) field_terms
                      (mk_global_app_named_args r (subst_to_inst_args subst))
  | _ -> spec_defn_term d

(* Build a term for the type of a field that is local to the current spec (see
   spec_defn_term_local) *)
let fctx_elem_type_local params elem =
  spec_defn_term_local params elem.felem_type_defn

(* Convert a spec definition to be global. NOTE: must be called inside
   the spec/module containing the definition *)
let globalize_spec_defn d =
  match d with
  | Local_Defn (id, fields) ->
     (try
         Global_Defn (Nametab.locate (qualid_of_ident id),
                      List.map (fun f ->
                                Nametab.locate (qualid_of_ident f)) fields,
                      mk_id_subst fields)
       with Not_found ->
         anomaly (str ("globalize_spec_defn: could not find name: " ^ Id.to_string id)))
  | _ -> raise dummy_loc (Failure "globalize_spec_defn")

(* Convert the type and (optional) of an fctx_elem to be global *)
let globalize_fctx_elem elem =
  { elem with
    felem_type_defn = globalize_spec_defn elem.felem_type_defn;
    felem_def_defn = map_opt globalize_spec_defn elem.felem_def_defn }

(* Convert all local types and definitions in a spec to global types
   and definitions. NOTE: must be called inside the spec/module with
   this fctx *)
let globalize_fctx fctx =
  List.map globalize_fctx_elem fctx


(***
 *** The internal representation of specs
 ***)

(* A spec is represented internally as having an optional global name
   (specs without names are called "anonymous", and are only for
   temporary calculations) and field contexts for the ops and for the
   axioms plus local theorems. *)
type spec = {
  spec_name : spec_globref option;
  spec_op_ctx : fctx;
  spec_axioms : fctx
}

(* The types (if flag = false) or the definitions (if flag = true) of
   the given named field in two different specs are not equal *)
exception FieldMismatch of Id.t * bool

(* Attempt to define the given field when it is not allowed *)
exception FieldDefNotAllowed of Id.t

(* Apply a name substitution to a spec *)
let subst_spec subst spec =
  { spec_name = None;
    spec_op_ctx = subst_fctx subst spec.spec_op_ctx;
    spec_axioms = subst_fctx subst spec.spec_axioms }

(* Create an anonymous empty spec *)
let empty_spec = { spec_name = None; spec_op_ctx = []; spec_axioms = [] }

(* Remove all the ops and axioms in spec2 from spec1, making sure that
   they have compatible types and definitions. Note that the result is
   not really a valid spec, since it could have some references to ops
   that no longer exist in it. Return both this resulting pseudo-spec
   as well as a list of the fctx_elems for any removed ops that were
   defined in spec1 but not in spec2 (see fctx_subtract) *)
let spec_subtract loc spec1 spec2 =
  let (new_op_ctx, removed_defs) =
    fctx_subtract
      (fun elem1 elem2 ->
       (* Check that the types of elem1 and elem2 are equal, in the
            context of spec1 *)
       if not (check_equal_term (fctx_params spec1.spec_op_ctx)
                                (fctx_elem_type elem1)
                                (fctx_elem_type elem2)) then
         raise loc (FieldMismatch (elem1.felem_id, false))

       (* If an op is defined in both spec and source, check that
            the definitions are equal *)
       else if fctx_elem_is_def elem1 &&
                 fctx_elem_is_def elem2 &&
                   not (check_equal_term (fctx_params spec1.spec_op_ctx)
                                         (fctx_elem_defn elem1)
                                         (fctx_elem_defn elem2))
       then
         raise loc (FieldMismatch (elem1.felem_id, false))
       else ()
      )
      spec1.spec_op_ctx spec2.spec_op_ctx
  in
  let (new_axioms, removed_thms) =
    fctx_subtract
      (fun elem1 elem2 ->
       (* Check that the types of elem1 and elem2 are equal, in the
            context of spec1 *)
       if not (check_equal_term (fctx_params spec1.spec_op_ctx)
                                (fctx_elem_type elem1)
                                (fctx_elem_type elem2)) then
         raise loc (FieldMismatch (elem1.felem_id, false))

       (* We don't care about equality of proofs, so no need to
            check definitions *)
       else ()
      )
      spec1.spec_axioms spec2.spec_axioms
  in
  ({ spec_name = None;
     spec_op_ctx = new_op_ctx;
     spec_axioms = new_axioms },
   removed_defs)

(* Named definitions *)
type named_def = Id.t * constr_expr

(* Change a declared op to a defined op in a spec *)
(* FIXME: break this down into smaller functions (e.g., on fctx's) *)
let add_spec_def spec (lid,body) =
  let id = located_elem lid in
  let loc = located_loc lid in
  (* Change the declared op lid in op_ctx to be defined *)
  let rec add_def_to_ctx op_ctx =
    match op_ctx with
    | [] ->
       (* Raise an exception if lid is not found *)
       raise loc Not_found
    | elem :: op_ctx' ->
       if Id.equal id elem.felem_id then
         if fctx_elem_is_def elem then
           (* Raise an exception if lid is already defined *)
           raise (located_loc lid) (FieldDefNotAllowed id)
         else
           fctx_elem_add_def elem (mk_term_spec_defn op_ctx' body) :: op_ctx'
       else
         elem :: add_def_to_ctx op_ctx'
  in
  { spec with
    spec_name = None;
    spec_op_ctx = add_def_to_ctx spec.spec_op_ctx }

(* Add a list of definitions of declared ops to a spec *)
let add_spec_defs spec defs =
  List.fold_left add_spec_def spec defs


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = ref (MPmap.empty)

(* Register a spec in the spec_table; this makes a spec named. NOTE:
   this is must be called *inside* the spec's module, after
   its axiom typeclass has been created *)
let globalize_spec spec spec_id =
  let _ = match spec.spec_name with
    | Some n -> anomaly (str "globalize_spec: spec already named!")
    | None -> ()
  in
  let spec_name = global_modpath (Nametab.locate (qualid_of_ident spec_id)) in
  let global_spec =
    { spec_name = Some spec_name;
      spec_op_ctx = globalize_fctx spec.spec_op_ctx;
      spec_axioms = globalize_fctx spec.spec_axioms } in
  (*
  Format.eprintf "\nglobalize_spec: ind (name = %s, id = %i)\n"
                 (MutInd.to_string ind) i
   *)
  spec_table := MPmap.add spec_name global_spec !spec_table;
  global_spec

(* Look up a spec and its spec_globref from a local spec reference *)
let lookup_spec_and_globref locref =
  let globref = lookup_spec_globref locref in
  (MPmap.find globref !spec_table, globref)

(* Look up a spec from a local spec reference *)
let lookup_spec locref = fst (lookup_spec_and_globref locref)


(***
 *** Building up the current spec
 ***)

(* The currrent spec being defined, if one exists, along with its
   local name *)
let current_spec : (spec * Id.t) option ref = ref None

(* There is no current spec *)
exception NoCurrentSpec

(* There is already a current spec *)
exception IsCurrentSpec

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Get the current spec or throw an exception *)
let get_current_spec loc =
  match !current_spec with
  | Some (spec,id) -> spec
  | None -> raise loc NoCurrentSpec

(* Update the current spec, if it exists, by applying f *)
let update_current_spec loc f =
  match !current_spec with
  | Some (spec,id) ->
     current_spec := Some (f spec, id)
  | None -> raise loc NoCurrentSpec

(* The op_ctx of the current spec *)
let current_op_ctx loc =
  (get_current_spec loc).spec_op_ctx

(* The parameters in the current spec *)
let current_spec_params loc =
  fctx_params (current_op_ctx loc)

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to the current spec, creating a type-class for it *)
let add_declared_op op_name op_type =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let _ = Format.eprintf "\nadd_declared_op: %s\n" (Id.to_string op_id) in

  (* Add a type-class op_name__class : Type := op_name : op_type *)
  let tp_defn = add_local_typeclass
                     (loc, field_class_id op_id) true (current_op_ctx loc)
                     [(op_name, op_type, false)] in

  update_current_spec
    loc
    (fun s ->
     { s with
       spec_op_ctx =
         fctx_cons op_id false tp_defn None s.spec_op_ctx })

(* Add an axiom to the current spec, creating a definition for its type *)
let add_axiom ax_name is_ghost ax_type =
  let ax_id = located_elem ax_name in
  let loc = located_loc ax_name in
  let _ = Format.eprintf "\nadd_axiom: %s\n" (Id.to_string ax_id) in
  (* Add a definition for ax_name__type : Prop := op_type *)
  let tp_defn = add_local_definition
                  (loc, field_type_id ax_id)
                  (current_op_ctx loc) (Some prop_expr) ax_type in
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axioms = fctx_cons ax_id is_ghost tp_defn None s.spec_axioms })

(* Add a defined op to the current spec, creating a type-class and def for it *)
let add_defined_op op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let op_ctx = current_op_ctx loc in
  let op_var_id = add_suffix_l op_name "var" in
  let _ = Format.eprintf "\nadd_defined_op: %s\n" (Id.to_string op_id) in

  (* Add a definition op_name : op_type := op_body *)
  let def_defn = add_local_definition op_name op_ctx (Some op_type) op_body in

  (* Add a type-class for op_name__class : Type := op_name__var : op_type *)
  let tp_defn =
    add_local_typeclass (loc, field_class_id op_id) true op_ctx
                        [(op_var_id, op_type, false)] in

  (* Add the new op to spec *)
  let _ =
    update_current_spec
      loc
      (fun s ->
       { s with
         spec_op_ctx =
           fctx_cons op_id false tp_defn (Some def_defn) s.spec_op_ctx }) in

  (* Add an axiom "op_name = op_name__var" to the resulting spec *)
  add_axiom
    (add_suffix_l op_name "eq") true
    (mk_ident_equality op_var_id op_name)


(* Complete the current spec, by creating its axiom type-class and
   registering it in the global spec table. No more axioms can be
   added to a spec once it has been completed. Return the globalized
   version of the current spec. *)
let complete_spec loc =
  match !current_spec with
  | None -> raise loc NoCurrentSpec
  | Some (spec, spec_id) ->
     let ax_fields =
       List.rev_map (fun elem ->
                     ((loc, elem.felem_id), fctx_elem_type elem, false))
                    spec.spec_axioms in
     let _ = add_typeclass (loc, spec_id) false (current_spec_params loc) ax_fields in
     globalize_spec spec spec_id

     (* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  if !current_spec = None then
    (current_spec := Some (empty_spec, located_elem spec_lid);
     begin_module spec_lid)
  else
    raise (located_loc spec_lid) IsCurrentSpec

(* Finish the interactive definition of a new spec by completing it
   and clearing current_spec; return the newly defined spec *)
let end_new_spec lid =
  let loc = located_loc lid in
  match !current_spec with
  | Some (spec, spec_id) ->
     if Id.equal spec_id (located_elem lid) then
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
  let spec_id = located_elem spec_lid in
  let loc = located_loc spec_lid in
  let saved_spec = !current_spec in
  let _ = current_spec := Some (empty_spec, spec_id) in
  let spec = within_module spec_lid
                           (fun () -> builder (); complete_spec loc) in
  let _ = current_spec := saved_spec in
  spec


(***
 *** Spec Imports
 ***)

(* Import an op from elem into the current spec, adding an instance of
   elem's old class in its previous spec if elem has a global type *)
let import_op loc elem =
  let params = current_spec_params loc in
  let _ =
    if fctx_elem_is_def elem then
      add_defined_op (loc, elem.felem_id)
                     (Some (fctx_elem_type_local params elem))
                     (fctx_elem_defn elem)
    else
      add_declared_op (loc, elem.felem_id)
                      (fctx_elem_type_local params elem)
  in
  if fctx_elem_has_global_type elem then
    add_term_instance (loc, Name (field_inst_id elem.felem_id))
                      (current_spec_params loc)
                      (fctx_elem_type elem)
                      (mk_var (loc, field_var_id elem.felem_id))
  else ()

(* Add all the ops from a given fctx; we fold right so each op can see
   the ops after it in fctx, which are the ones it depends on (since
   fctx's are stored backwards) *)
let import_ops loc fctx =
  List.fold_right (fun elem () -> import_op loc elem) fctx ()

(* Add all the axioms from a given fctx *)
let import_axioms loc fctx =
  let params = current_spec_params loc in
  List.fold_right (fun elem () ->
                   if elem.felem_is_ghost then () else
                     add_axiom (loc, elem.felem_id) false
                               (fctx_elem_type_local params elem))
                  fctx ()

(* Import a spec into the current spec *)
let import_spec loc im_spec =
  (* Remove any ops/axioms in spec from im_spec *)
  let (real_im_spec, im_new_defs) =
    spec_subtract loc im_spec (get_current_spec loc) in
  (* im_spec cannot define any existing ops in spec *)
  let _ =
    match im_new_defs with
    | [] -> ()
    | elem :: _ -> raise loc (FieldDefNotAllowed elem.felem_id)
  in
  (* For each op, add the op to the current spec, and also add an
     instance of the previous op type *)
  import_ops loc real_im_spec.spec_op_ctx;
  import_axioms loc real_im_spec.spec_axioms


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

(* Resolve a name translation into a name substitution for a spec *)
let resolve_name_translation spec xlate : field_subst =
  concat_map (fun elem ->
              let id = elem.felem_id in
              (*
              let _ = Format.eprintf "resolve_name_translation: mapping field %s\n"
                                     (Id.to_string id) in
               *)
              match translate_id xlate id with
              | Some id' ->
                 (*
                 let _ = Format.eprintf "resolve_name_translation: mapped field %s to %s\n"
                                        (Id.to_string id) (Id.to_string id') in
                  *)
                 if fctx_elem_is_def elem then
                   (* If id is a def, also map id__eq -> id'__eq *)
                   [(id, id'); (add_suffix id "eq", add_suffix id' "eq")]
                 else
                   [(id, id')]
              | None -> [])
             spec.spec_op_ctx
  @ filter_map (fun elem ->
                let id = elem.felem_id in
                match translate_id xlate id with
                | Some id' ->
                   (* Filter out mappings on "__eq" axioms *)
                   if has_suffix id "__eq" then None else
                     Some (id, id')
                | None -> None)
               spec.spec_axioms


(***
 *** Spec Instances
 ***)

(* Represents an instance of inst_spec in the current spec *)
type spec_instance = {
  inst_spec : spec_locref;
  inst_op_subst : field_subst;
  inst_ax_subst : field_subst
}

(* Substitute into a spec_instance *)
let subst_spec_inst subst inst =
  { inst with
    inst_op_subst = subst_field_subst subst inst.inst_op_subst;
    inst_ax_subst = subst_field_subst subst inst.inst_ax_subst }

(* Build the identity instance of spec (with local name locref) in itself *)
let make_id_instance locref spec =
  { inst_spec = locref;
    inst_op_subst = subst_from_fctx spec.spec_op_ctx;
    inst_ax_subst = subst_from_fctx spec.spec_axioms }

(* FIXME HERE: write add_instance *)


(***
 *** Spec Morphisms
 ***)

(* Could not find a morphism from the given reference *)
exception MorphismNotFound of reference

(* A morphism contains source and target specs, a name substitution
   mapping ops from the former to the latter, and a global reference
   to an interpretation function that builds an instance of the source
   spec's type-class from that of the target *)
type morphism = {
  morph_source : spec;
  morph_target : spec;
  morph_subst : field_subst;
  morph_interp : constant
}

(* The implicit argument name for the spec argument of a morphism
   interpretation function *)
(* let morph_spec_arg_id = Id.of_string "Spec" *)

(* Global table of named morphisms *)
let morphism_table = ref (Cmap.empty)

(* Register a morphism in the morphism table *)
let register_morphism morph =
  morphism_table := Cmap.add morph.morph_interp morph !morphism_table

(* Look up a morphism by local reference *)
let lookup_morphism r =
  try
    match Nametab.locate (located_elem (qualid_of_reference r)) with
    | ConstRef c -> Cmap.find c !morphism_table
    | _ -> raise (loc_of_reference r) (MorphismNotFound r)
  with Not_found ->
    raise (loc_of_reference r) (MorphismNotFound r)


(* FIXME HERE: make a function that sets up the proof obligations for
   a morphism, and then adds it to a global morphism table when
   finished *)
(* let start_morphism morph_name xlate *)


(* Counter for building fresh spec names in apply_morphism *)
let morphism_spec_counter = ref 1

(* Build a fresh id for the result of a morphism *)
let mk_morph_spec_id () =
  let n = !morphism_spec_counter in
  let _ = morphism_spec_counter := n+1 in
  Id.of_string ("morph_spec__" ^ string_of_int n)

(* Apply morphism to spec, yielding (subst (spec - source) ++ target);
   i.e., remove from spec any ops and axioms listed in the source of
   the morphism, apply the morphism substitution to the result, and
   then add back in the ops and axioms listed in the target spec. The
   op_ctx in the result are topologically sorted so that it is valid,
   i.e., so that no op refers to a later one. The resulting spec is
   built in a new module (whose name comes from mk_morph_spec_id), and
   derived instances are added of the source and target specs of the
   morphism in this new spec. The new spec object is then returned,
   along with a local reference to it.

   Another way to think about morphism application is that we are
   applying the morphism substitution to the input spec, which removes
   any fields in its domain and replaces them with their correponding
   fields in the co-domain of the substitution. *)
let apply_morphism loc morph spec =
  let spec_id = mk_morph_spec_id () in
  let (rem_spec, removed_defs) = spec_subtract loc spec morph.morph_source in
  let _ =
    (* If an op is defined in spec and not in source, make sure it
       does not become defined in target *)
    (* NOTE: a more permissive check would instead just require
       target.op = spec.op *)
    List.iter
      (fun elem ->
       match fctx_lookup morph.morph_target.spec_op_ctx
                         (subst_id morph.morph_subst elem.felem_id)
       with
       | Some elem_t ->
          if fctx_elem_is_def elem_t then
            raise loc (FieldDefNotAllowed elem.felem_id)
          else ()
       | None -> ())
      removed_defs
  in

  (* Append the target ops and then sort *)
  let new_op_ctx =
    stable_reverse_topo_sort loc (fun e -> e.felem_id) Id.equal fctx_elem_deps
                             (rem_spec.spec_op_ctx
                              @ morph.morph_target.spec_op_ctx) in
  (* Append the target axioms (no need to sort; axioms do not depend
     on each other) *)
  let new_axioms = rem_spec.spec_axioms @ morph.morph_target.spec_axioms in

  (* Now build the new spec module *)
  let new_spec =
    within_named_spec
      (loc, spec_id)
      (fun () ->
       import_spec loc { spec_name = None;
                         spec_op_ctx = new_op_ctx;
                         spec_axioms = new_axioms }

       (* FIXME HERE: add derived instances! (maybe return them as well?) *)
      )
  in
  (new_spec, qualid_of_ident spec_id)


(***
 *** Spec Terms
 ***)

(* Spec terms are syntactic forms for building specs from existing
   specs *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * name_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * reference
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs of spec_term * (lident * Constrexpr.constr_expr) list

(* Get the source location of a spec_term *)
let rec spec_term_loc st =
  match st with
  | SpecRef r -> loc_of_reference r
  | SpecXlate (st', _) -> spec_term_loc st'
  | SpecSubst (st', _) -> spec_term_loc st'
  | SpecAddDefs (st', _) -> spec_term_loc st'

(* Interpret a spec term into a spec plus an instance in this returned
   spec of the outer-most spec reference or morphism application *)
let rec interp_spec_term sterm : spec * spec_instance =
  match sterm with
  | SpecRef r ->
     (try
         let locref = spec_locref_of_ref r in
         let spec = lookup_spec locref in
         (spec, make_id_instance locref spec)
       with Not_found ->
         user_err_loc (spec_term_loc sterm, "_",
                       str ("No spec named " ^ string_of_reference r)))
  | SpecXlate (sterm', xlate) ->
     let (spec, inst) = interp_spec_term sterm' in
     let subst = resolve_name_translation spec xlate in
     (*
     let _ =
       List.iter (fun (id_from, id_to) ->
                   Format.eprintf "Translating %s to %s\n"
                                  (Id.to_string id_from)
                                  (Id.to_string id_to)) subst in
      *)
     (subst_spec subst spec, subst_spec_inst subst inst)
  | SpecSubst (sterm', morph_ref) ->
     let (spec, inst) = interp_spec_term sterm' in
     let loc = loc_of_reference morph_ref in
     let morph = lookup_morphism morph_ref in
     (* FIXME HERE: figure out what to do with inst! *)
     let (new_spec, new_locref) = apply_morphism loc morph spec in
     (new_spec, make_id_instance new_locref new_spec)
  | SpecAddDefs (sterm', defs) ->
     let (spec, inst) = interp_spec_term sterm' in
     (add_spec_defs spec defs, inst)

(* Interpret a spec term and import it into the current spec *)
let import_spec_term st =
  let (im_spec, inst) = interp_spec_term st in
  (* FIXME HERE: figure out what to do with inst! *)
  import_spec (spec_term_loc st) im_spec


(***
 *** Additions to the Coq parser
 ***)

(* Run f, catching any exceptions and turning them into user_errors *)
(* FIXME HERE: actually write this! *)
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
  | [ spec_term(st) "{" name_translation(xlate) "}" ] -> [ SpecXlate (st, xlate) ]
  | [ spec_term(st) "[" global(morph_ref) "]" ] -> [ SpecSubst (st, morph_ref) ]
  | [ spec_term(st) "with" spec_term_defs(defs) ] -> [ SpecAddDefs (st, defs) ]
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
                                 (fun () -> import_spec_term st))) ]

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
           (fun () -> add_axiom (dummy_loc,id) false tp) ]

  (* Import a spec term *)
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term st) ]

END
