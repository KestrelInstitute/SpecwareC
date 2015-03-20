
DECLARE PLUGIN "specware"

open Names
open Loc
open Libnames
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
  let get_node_by_key_help k j =
    if j > Array.length arr then None
    else if key_eq k (key arr.(j)) then Some j
    else get_node_by_key_help k (j+1) in
  let get_node_by_key k = get_node_by_key_help k 0 in
  (* Perform a DFS to build the transitive closure of deps *)
  let get_node_deps path_to_i i =
    if visited.(i) then
      arr_deps.(i)
    else if List.mem i path_to_i then
      raise loc (TopoCircularity i)
    else
      let i_immed_deps = filter_map get_node_by_key (deps arr.(i)) in
      let i_deps = concat_map (get_node_deps i::path_to_i) i_immed_deps in
      visited.(i) <- true;
      arr_deps.(i) <- i_deps;
      i::i_deps
  in
  let index_arr = Array.init (List.length l) id in
  Array.to_list
    (Array.map (fun i -> arr.(i))
               (Array.stable_sort
                  (fun i j ->
                   if List.mem j arr_deps.(i) then 1
                   else if List.mem i arr_deps.(j) then -1
                   else j-i)
                  index_arr))


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
  CRef (Qualid (loc, mk_qualid dir id), None)

(* Get a string for a global reference *)
let global_to_string gr =
  match gr with
  | VarRef v -> raise dummy_loc (Failure "global_to_string")
  | ConstRef c -> Constant.to_string c
  | IndRef i -> MutInd.to_string i
  | ConstructRef _ -> raise dummy_loc (Failure "global_to_string")

(* Turn a global reference into a local one *)
(* FIXME: find a better way than using strings! *)
let qualid_of_global gr =
  qualid_of_string (global_to_string gr)

(* Build an expression for a global applied to named implicit args *)
let mk_global_app_named_args gr args =
  mk_ref_app_named_args (Qualid (qualid_of_global gr)) args

(* Build the expression t1 = t2 *)
let mk_equality t1 t2 =
  CApp (loc,
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
   normal type-class in Prop (if false) *)
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
                             Constructors [false, (id, Constrexpr_ops.mkCProdN
                                                         (located_loc id)
                                                         params tp)]
                          | _ -> raise (located_loc class_id) (Failure "add_typeclass")
                        else
                          RecordDecl (None, List.map mk_record_field fields)),
                       []]))

(* Add an instance using the given record fields *)
let add_instance inst_name inst_tp inst_fields =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  Some (true,
                        CRecord (loc, None,
                                 List.map (fun id -> Ident (loc, id))
                                          inst_fields)),
                  None))

(* Begin an interactively-defined instance *)
let begin_instance inst_name inst_tp =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  None, None))

(* Begin a new module *)
let begin_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []));

(* End the current module, which should have name mod_name *)
let end_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacEndSegment mod_name);

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
    vernac_check_may_eval
      None None
      (mkCProdN
         dummy_loc
         params
         (CCast (dummy_loc,
                 CApp (loc,
                       (None, mk_reference ["Coq"; "Init"; "Logic"]
                                           (Id.of_string "eq_refl")),
                       [(t1, None)]),
                 mk_equality t1 t2)));
    true
  with UserError _ -> false


(***
 *** Global and local references to specs
 ***)

(* FIXME: figure out how to get good error messages in the lookup
   functions! *)

(* A local reference to a spec is a qualid pointing to its module *)
type spec_locref = qualid

(* Build a spec_locref from a local identifier *)
let spec_locref_of_id id = qualid_of_id id

(* Return a qualid that points to field fname in spec locref *)
let field_in_spec locref fname =
  qualid_cons locref fname

(* A global reference to a spec is a global reference to the spec's
   module *)
type spec_globref = module_path

(* Lookup the global reference to a spec from a local reference *)
let lookup_spec_globref locref =
  Modintern.lookup_module locref

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
let rec eq_subst s1 s2 =
  match (s1, s2) with
  | ([], []) -> true
  | ((id1, id1') :: s1', (id2, id2') :: s2') ->
     Id.equal id1 id2 && Id.equal id1' id2' && eq_subst s1' s2'

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

(* Turn a name substitution into a list of (name,value) pairs, where
   value is a term expression; omit pairs where name = value *)
let subst_to_args subst =
  List.filter_map
    (fun (id_from, id_to) ->
     if Id.equal id_from id_to then None else
       Some (field_var_id id_from, mk_var (dummy_loc, id_to)))
    subst


(***
 *** Field Contexts
 ***)

(* A field context specifies a list of named fields, each of which has
   a type and an optional definition. Types and definitions are given
   as global references to existing definitions applied to some number
   of named arguments, the latter being given as a name substitution
   mapping the argument names to earlier fields in the context.

   NOTE: field contexts are stored backwards, in that the "earlier"
   fields are stored later in the list; i.e., fields can only refer to
   fields later in a field context. This is to make it easy to add new
   fields as we go *)
type glob_defn = | Defn of global_reference * field_subst
type fctx_elem = | FCtx_Elem of Id.t * glob_defn * glob_defn option
type fctx = fctx_elem list

(* Equality on global definitions *)
let eq_glob_defn d1 d2 =
  match (d1, d2) with
  | (Defn (r1, s1), Defn (r2, s2)) ->
     eq_gr r1 r2 && eq_subst s1 s2

(* Get the fields referenced by the args of a glob_defn *)
let glob_defn_deps d =
  match d with
  | Defn (_, args) -> List.map snd args

(* Turn a global definition into a term *)
let glob_defn_term d =
  match d with
  | Defn (r, subst) -> mk_global_app_named_args r (subst_to_args subst)

(* Accessors for fctx_elems *)
let fctx_elem_id fctx_elem =
  match fctx_elem with FCtx_Elem (id, _, _) -> id
let fctx_elem_type_defn fctx_elem =
  match fctx_elem with FCtx_Elem (_, tp, _) -> tp
let fctx_elem_glob_defn fctx_elem =
  match fctx_elem with FCtx_Elem (_, _, d) -> d

(* Return true iff an fctx_elem is defined *)
let fctx_elem_is_def elem =
  match fctx_elem_glob_defn elem with
  | Some _ -> true
  | None -> false

(* Build a term for the type of a field; this type depends on the
   fields in the fctx, i.e., it must be inside the parameter context
   returned by fctx_params for the suffix after elem of the fctx elem
   occurs in (which is really the "earlier" elements of the fctx,
   remembering that fctx's are stored backwards) *)
let fctx_elem_type elem = glob_defn_term (fctx_elem_type_defn elem)

(* Build a term for the definition of a field; this type depends on
   the fields in the fctx (see fctx_elem_type) *)
let fctx_elem_defn elem =
  match fctx_elem_glob_defn elem with
  | Some d -> glob_defn_term d
  | None -> raise dummy_loc (Failure "fctx_elem_defn")

(* Find a named field in an fctx, returning None if not found *)
let rec fctx_lookup fctx f =
  match fctx with
  | [] -> None
  | elem :: fctx' ->
     if Id.equal f (fctx_elem_id elem) then
       Some elem
     else
       fctx_lookup fctx' f

(* Apply a name substitution to a definition *)
let subst_glob_defn subst d =
  match d with
  | Defn (r, args) -> Defn (r, subst_field_subst subst args)

(* Apply a name substitution to an optional definition *)
let subst_glob_defn_opt subst d_opt =
  match d_opt with
  | Some d -> subst_glob_defn subst d
  | None -> None

(* Apply a name substitution to an fctx_elem *)
let subst_fctx_elem subst elem =
  match elem with
  | FCtx_Elem (id, tp, d) ->
     FCtx_Elem (subst_id subst id, subst_glob_defn subst tp,
                subst_glob_defn_opt subst d)

(* Apply a name substitution to an fctx *)
let subst_fctx subst fctx =
  List.map subst_fctx_elem fctx

(* Build the identity substitution for the fields in an fctx
   (remembering that field contexts are stored backwards) *)
let subst_from_fctx fctx =
  List.rev_map (fun elem -> (fctx_elem_id elem, fctx_elem_id elem)) fctx

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
               Id.equal (fctx_elem_id elem1) (fctx_elem_id elem2) &&
                 let _ = check_fun elem1 elem2 in
                 let _ = if fctx_elem_is_def elem1
                            && ~(fctx_elem_is_def elem2) then
                           def_subst := elem1 :: def_subst
                         else () in
                 true)
              fctx2))
      fctx1 in
  (ret_fctx, def_subst)

(* Cons a field to a field context, where we assume the type and
   definition for the field have already been defined in the local
   module; class_p and defn_p specify respectivly whether the field
   has a type-class (versus a regular type) and a definition *)
let fctx_cons_local id class_p defn_p fctx =
  (* Get the global name for the type *)
  let type_global =
    Nametab.locate (qualid_of_id (if class_p then field_class_id id
                                  else field_type_id id))
  in
  (* Build the arguments for the type and optional definition *)
  let args = subst_from_fctx fctx in
  FCtx_Elem (id, Defn (type_global, args),
             if defn_p then
               Some (Nametab.locate (qualid_of_id id))
             else None)

(* Convert a single fctx_elem to an implicit class assumption *)
let fctx_elem_to_param fctx_elem =
  mk_implicit_assum (fctx_elem_var_id fctx_elem)
                    (mk_var (dummy_loc, fctx_elem_class_id fctx_elem))

(* Convert an fctx to a list of class parameters, one for each field
   in the context (remember: fctx is reversed) *)
let fctx_params fctx =
  List.rev_map fctx_elem_to_param fctx


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
  { spec_op_ctx = subst_fctx subst spec.spec_op_ctx;
    spec_axioms = subst_fctx subst spec.axioms }

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
       if ~(check_equal_term (fctx_params spec1.spec_op_ctx)
                             (fctx_elem_type elem1)
                             (fctx_elem_type elem2)) then
         raise loc (FieldMismatch (fctx_elem_id elem1, false))

       (* If an op is defined in both spec and source, check that
            the definitions are equal *)
       else if fctx_elem_is_def elem1 &&
                 fctx_elem_is_def elem2 &&
                   ~(check_equal_term (fctx_elem_def elem1)
                                      (fctx_elem_def elem2))
       then
         raise loc (FieldMismatch (fctx_elem_id elem1, false))
       else ()
      )
      spec1.spec_op_ctx spec2.spec_op_ctx
  in
  ({ spec_name = None;
     spec_op_ctx = new_op_ctx;
     spec_axioms =
       fctx_subtract
         (fun elem1 elem2 ->
          (* Check that the types of elem1 and elem2 are equal, in the
            context of spec1 *)
          if ~(check_equal_term (fctx_params spec1.spec_op_ctx)
                                (fctx_elem_type elem1)
                                (fctx_elem_type elem2)) then
            raise loc (FieldMismatch (fctx_elem_id elem1, false))

          (* We don't care about equality of proofs, so no need to
            check definitions *)
          else ()
         )
         spec1.spec_axioms spec2.spec_axioms },
   removed_defs)

(* Named definitions *)
type named_def = Id.t * constr_expr option * constr_expr

(* Counter for building fresh definition names in add_spec_def *)
(* FIXME: unify these fresh names with apply_morphism *)
let def_name_counter = ref 1

(* Change a declared op to a defined op for a spec that is not the
   current spec; this generates a new definition with a fresh,
   generated name to the current module *)
let add_spec_def spec (lid,tp_opt,body) =
  let id = located_elem lid in
  let tp =
    match tp_opt with
    | Some tp -> tp
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let def_n = !def_name_counter in
  let _ = def_name_counter := def_n + 1 in
  let def_id = Id.of_string ("local_def__" ^ string_of_int n) in
  let tp_id = Id.of_string ("local_def__" ^ string_of_int n ^ "__type") in
  let rec helper op_ctx =
    match op_ctx with
    | [] -> raise Not_found
    | elem :: op_ctx' ->
       if Id.equal id (fctx_elem_id elem) then
         if fctx_elem_id_def elem then
           raise (located_loc lid) (FieldDefNotAllowed id)
         else
           let _ = add_definition def_id (fctx_params op_ctx') (Some tp) body in
           let _ =
             if tp_opt = None then
               add_definition tp_id (fctx_params op_ctx') (Some type_expr)
             else () in
           FCtx_Elem (id, Nametab.locate (qualid_of_id tp_id),
                      Some (Nametab.locate (qualid_of_id def_id)))

(* FIXME HERE: think about only adding defs in the current spec... *)
let add_spec_defs spec defs =
  List.fold_left add_spec_def spec defs


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = ref (MPmap.empty)

(* Register a spec in the spec_table; this makes a spec named. NOTE:
   this is normally called *outside* the spec's module *)
let register_global_spec spec spec_locref =
  let _ = match spec.spec_name with
    | Some n -> anomaly (str "register_global_spec: spec already named!")
    | None -> ()
  in
  let spec_name = lookup_spec_globref spec_locref in
  let named_spec = { spec with spec_name = Some spec_name } in
  (*
  Format.eprintf "\nregister_global_spec: ind (name = %s, id = %i)\n"
                 (MutInd.to_string ind) i
   *)
  spec_table := MPmap.add spec_name named_spec !spec_table;
  named_spec

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
let set_current_spec loc f =
  match !current_spec with
  | Some (spec,id) ->
     current_spec := Some (f spec, id)
  | None -> raise loc NoCurrentSpec

(* The parameters in the current spec *)
let current_spec_params loc =
  fctx_params (get_current_spec loc).spec_op_ctx

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to the current spec, creating a type-class for it *)
let add_declared_op op_name op_type =
  let op_id = located_elem op_name in
  let loc = localted_loc op_name in
  add_typeclass (loc, field_class_id op_id) true
                (current_spec_params loc) [(op_name, op_type, false)];
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_op_ctx = fctx_cons_local op_name true false
                                     !current_spec.spec_op_ctx })

(* Add an axiom to the current spec, creating a definition for its type *)
let add_axiom ax_name ax_type =
  let ax_id = located_elem ax_name in
  add_definition (located_loc ax_name, field_type_id ax_id)
                 (current_spec_params loc) prop_expr ax_type;
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axioms = fctx_cons ax_id false false
                               !current_spec.spec_axioms })

(* Add a defined op to the current spec, creating a type-class and def for it *)
let add_defined_op op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let params = current_spec_params loc in
  let op_var_id = add_suffix_l op_name "var" in

  (* Add a definition op_name = op_body *)
  add_definition op_name params op_type_opt op_body;

  (* Add a type-class for op_name__var : op_type *)
  add_typeclass (field_class_name op_id) true params
                [(op_var_id, op_type, false)] ;

  (* Add the new op to spec *)
  let _ =
    update_current_spec
      loc
      (fun s ->
       { !current_spec with
         spec_op_ctx = fctx_cons op_id true true !current_spec.spec_op_ctx }) in

  (* Add an axiom "op_name = op_name__var" to the resulting spec *)
  add_axiom
    (add_suffix_l op_name "eq")
    (mk_ident_equality op_var_id op_name)


(* Add an op from an fctx_elem to the current spec *)
let add_fctx_elem_op loc elem =
  if fctx_elem_is_def elem then
    add_defined_op (loc, fctx_elem_id elem)
                   (Some (fctx_elem_type elem))
                   (fctx_elem_defn elem)
  else
    add_declared_op (loc, fctx_elem_id elem)
                    (fctx_elem_type elem)

(* Add all the ops from a given fctx; we fold right so each op can see
   the ops after it in fctx, which are the ones it depends on (since
   fctx's are stored backwards) *)
let add_fctx_ops loc fctx =
  List.fold_right (fun elem () -> add_fctx_elem_op loc elem) fctx ()

(* Add all the axioms from a given fctx *)
let add_fctx_axioms loc fctx =
  List.fold_right (fun elem () ->
                   add_axiom (loc, fctx_elem_id elem) (fctx_elem_type elem))
                  fctx ()

(* Complete the current spec, by creating its axiom type-class. No
   more axioms can be added to a spec once it has been completed. *)
let complete_spec loc =
  match !current_spec with
  | None -> raise loc NoCurrentSpec
  | Some (_, spec_id) ->
     add_typeclass (loc, spec_name) false
                   (current_spec_params ())
                   (List.rev_map
                      (fun ax_name ->
                       (ax_name, mk_var (loc, axiom_type_id ax_name), false))
                      ax_fields)

(* Import a spec into the current spec *)
let import_spec loc im_spec =
  (* Remove any ops/axioms in spec from im_spec *)
  let (real_im_spec, im_new_defs) = spec_subtract im_spec (get_current_spec loc) in
  (* im_spec cannot define any existing ops in spec *)
  let _ =
    match im_new_defs with
    | [] -> ()
    | elem :: _ -> raise loc (FieldDefNotAllowed (fctx_elem_id elem))
  in
  add_fctx_ops real_im_spec.spec_op_ctx;
  add_fctx_axioms real_im_spec.spec_axioms

(* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  if !current_spec = None then
    (current_spec := Some (empty_spec, located_elem spec_lid);
     begin_module spec_lid)
  else
    raise (lococated_loc spec_lid) IsCurrentSpec

(* Finish the interactive definition of a new spec by completing it,
   registering it in the global table, and clearing current_spec;
   return the newly defined spec *)
let end_new_spec lid =
  let loc = located_loc lid in
  match !current_spec with
  | Some (spec, id) ->
     if Id.equal id (located_elem lid) then
       (complete_spec ();
        end_module lid;
        register_global_spec spec (spec_locref_of_id (located_elem lid));
        current_spec := None)
       spec
     else
       raise loc WrongCurrentSpecName
  | None -> raise loc NoCurrentSpec

(* Build a new spec in a new module called spec_id, calling builder
   inside that new module to build the spec; unlike begin_new_spec,
   within_named spec can be nested inside another spec definition *)
let within_named_spec spec_id builder =
  let save_spec = !current_spec in
  let _ = current_spec := Some (empty_spec, spec_id) in
  let _ = within_module spec_id builder in
  let spec =
    match !current_spec with
    | None -> anomaly (str "within_named_spec: current_spec has become empty!")
    | Some (spec, _) -> spec
  in
  let _ = current_spec := save_spec in
  register_global_spec spec (spec_locref_of_id spec_id)


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
     if id_from = id_to then Some id_to else
       translate_id xlate' id
  | NameXPrefix (pre_from, pre_to) :: xlate' ->
     let pre_len = String.length pre_from in
     let id_str = Id.to_string id in
     if String.sub id_str 0 pre_len = pre_from then
       Some
         (Id.from_string
            (String.concat "" [pre_to,
                               String.sub id_str pre_len
                                          (String.length id_str - pre_len)]))
     else
       translate_id xlate' id

(* Resolve a name translation into a name substitution for a spec *)
let resolve_name_translation spec xlate : field_subst =
  concat_map (fun elem ->
              match translate_id xlate (fctx_elem_id elem) with
              | Some id' ->
                 if fctx_elem_is_def elem then
                   (* If id is a def, also map id__eq -> id'__eq *)
                   [(id, id'), (add_suffix id "eq", add_suffix id' "eq")]
                 else
                   [(id, id')]
              | None -> [])
             spec.spec_op_ctx
  @ filter_map (fun elem ->
                match translate_id xlate (fctx_elem_id elem) with
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
  inst_ax_subst : field_subts
}

(* Substitute into a spec_instance *)
let subst_spec_inst subst inst =
  { inst with
    inst_op_subst = subst_field_subst subst inst.inst_op_subst;
    inst_ax_subst = subst_field_subst subst inst.inst_ax_subst }

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
  let qualid = qualid_of_reference r in
  try
    match Nametab.locate with
    | Constref c -> Cmap.find c !morphism_table
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
  let (rem_spec, removed_defs) = spec_subtract spec morph.morph_source in
  let _ =
    (* If an op is defined in spec and not in source, make sure it
       does not become defined in target *)
    (* NOTE: a more permissive check would instead just require
       target.op = spec.op *)
    List.iter
      (fun elem ->
       match fctx_lookup morph.morph_target.spec_op_ctx
                         (subst_id morph.morph_subst
                                   (fctx_elem_id elem))
       with
       | Some elem_t ->
          if fctx_elem_is_def elem_t then
            raise loc (FieldDefNotAllowed (fctx_elem_id elem))
          else ()
       | None -> ())
      removed_defs
  in

  (* Append the target ops and then sort *)
  let new_op_ctx =
    stable_reverse_topo_sort fctx_elem_id Id.equal glob_defn_deps
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
                         spec_axioms = new_axioms };
       complete_spec loc;

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
         (lookup_spec locref,
          make_id_instance locref spec)
       with Not_found ->
         user_err_loc (spec_term_loc sterm, "_",
                       str ("No spec named " ^ string_of_reference r)))
  | SpecXlate (sterm', xlate) ->
     let (spec, inst) = interp_spec_term sterm' in
     let subst = resolve_name_translation spec xlate in
     (subst_spec subst spec, subst_spec_inst subst inst)
  | SpecSubst (sterm', morph_ref) ->
     let (spec, inst) = interp_spec_term sterm' in
     let morph = lookup_morphsim morph_ref in
     (* FIXME HERE: figure out what to do with inst! *)
     let (new_spec, new_locref) = apply_morphism morph spec in
     (new_spec, make_id_instance new_locref new_spec)
  | SpecAddDefs (sterm', defs) ->
     let (spec, inst) = interp_spec_term sterm' in
     (add_spec_defs spec defs, inst)

(* Interpret a spec term and import it into the current spec *)
let import_spec_term st =
  let (im_spec, inst) = interp_spec_term st in
  (* FIXME HERE: figure out what to do with inst! *)
  import_spec im_spec


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
  | [ ident(id) ":=" constr(def) ";" import_defs(rest) ] -> [ ((loc,id), def)::rest ]
  | [ ident(id) ":=" constr(def) ] -> [ [(loc,id), def] ]
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
            within_named_spec (loc, spec_name)
                              (fun () ->
                               import_spec_term st;
                               complete_spec ())) ]

  (* Start an interactive spec definition *)
  | [ "Spec" ident(spec_name) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            begin_new_spec (loc, spec_name)) ]

  (* End an interactive spec definition *)
  | [ "Spec" "End" ident(spec_name) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            end_new_spec (loc, spec_name)) ]

  (* Add a declared op *)
  | [ "Spec" "Variable" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_declared_op (loc,id) tp) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" ident(id) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (loc,id) (Some tp) body) ]
  (* Add a defined op without a type *)
  | [ "Spec" "Definition" ident(id) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (loc,id) None body) ]

  (* Add an axiom *)
  | [ "Spec" "Axiom" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_axiom (loc,id) tp) ]

  (* Import a spec term *)
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term st) ]

END
