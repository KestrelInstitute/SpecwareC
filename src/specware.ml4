
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
let rec stable_reverse_topo_sort key key_eq deps l =
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
      Pervasives.raise (TopoCircularity i)
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

(* Perform some operation(s) inside a newly-defined module *)
let within_module mod_name f =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []));
  let ret = f () in
  interp (loc, VernacEndSegment mod_name);
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
type glob_defn = | Defn of global_reference * name_subst
type fctx_elem = | FCtx_Elem of Id.t * glob_defn * glob_defn option
type fctx = fctx_elem list

(* Equality on global definitions *)
let eq_glob_defn d1 d2 =
  match (d1, d2) with
  | (Defn (r1, s1), Defn (r2, s2)) ->
     eq_gr r1 r2 && eq_subst s1 s2

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
  | Defn (r, args) -> Defn (r, subst_name_subst subst args)

(* Apply a name substitution to an optional definition *)
let subst_glob_defn_opt subst d_opt =
  match d_opt with
  | Some d -> subst_glob_defn subst d
  | None -> None

(* Apply a name substitution to an fctx_elem *)
let subst_fctx_elem subst elem =
  match elem with
  | FCtx_Elem (id, tp, d) ->
     FCtx_elem (subst_id subst id, subst_glob_defn subst tp,
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
let fctx_to_param fctx_elem =
  mk_implicit_assum (fctx_elem_var_id fctx_elem)
                    (mk_var (dummy_loc, fctx_elem_class_id fctx_elem))

(* Convert an fctx to a list of class parameters, one for each field
   in the context (remember: fctx is reversed) *)
let fctx_params fctx =
  List.rev_map fctx_to_param fctx


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

(* Apply a name substitution to a spec *)
let subst_spec subst spec =
  { spec_op_ctx = subst_fctx subst spec.spec_op_ctx;
    spec_axioms = subst_fctx subst spec.axioms }

(* Create an anonymous empty spec *)
let empty_spec = { spec_name = None; spec_op_ctx = []; spec_axioms = [] }

(* The types (if flag = false) or the definitions (if flag = true) of
   the given named field in two different spec are not equal *)
exception FieldMismatch of Id.t * bool

(* Remove all the ops and axioms in spec2 from spec1, making sure that
   they have compatible types and definitions. Note that the result is
   not really a valid spec, since it could have some references to ops
   that no longer exist in it. Return both this resulting pseudo-spec
   as well as a list of the fctx_elems for any removed ops that were
   defined in spec1 but not in spec2 (see fctx_subtract) *)
let spec_subtract spec1 spec2 =
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

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to a spec, creating a type-class for it *)
let add_declared_op spec op_name op_type =
  let op_id = located_elem op_name in
  let loc = localted_loc op_name in
  add_typeclass (loc, field_class_id op_id) true
                (fctx_params spec.spec_op_ctx) [(op_name, op_type, false)];
  { spec with
    spec_op_ctx = fctx_cons_local op_name true false spec.spec_op_ctx }

(* Add an axiom to a spec, creating a definition for its type *)
let add_axiom spec ax_name ax_type =
  let ax_id = located_elem ax_name in
  add_definition (located_loc ax_name, field_type_id ax_id)
                 (fctx_params spec.spec_op_ctx) prop_expr ax_type;
  { spec with
    spec_axioms = fctx_cons ax_id false false spec.spec_axioms }

(* Add a defined op to a spec, creating a type-class and def for it *)
let add_defined_op spec op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let params = fctx_params spec.spec_op_ctx in
  let op_var_id = add_suffix_l op_name "var" in

  (* Add a definition op_name = op_body *)
  add_definition op_name params op_type_opt op_body;

  (* Add a type-class for op_name__var : op_type *)
  add_typeclass (field_class_name op_id) true params
                [(op_var_id, op_type, false)] ;

  (* Add the new op to spec *)
  let spec' = 
    { spec with
      spec_op_ctx = fctx_cons op_id true true spec.spec_op_ctx } in

  (* Add an axiom "op_name = op_name__var" to the resulting spec *)
  add_axiom
    spec'
    (add_suffix_l op_name "eq")
    (mk_ident_equality op_var_id op_name)


(* Add an op from an fctx_elem *)
let add_fctx_elem_op spec elem =
  if fctx_elem_is_def elem then
    add_defined_op spec (fctx_elem_id elem)
                   (Some (fctx_elem_type elem))
                   (fctx_elem_defn elem)
  else
    add_declared_op spec (fctx_elem_id elem)
                    (fctx_elem_type elem)

(* Add all the ops from a given fctx; we fold right so each op can see
   the ops after it in fctx, which are the ones it depends on (since
   fctx's are stored backwards) *)
let add_fctx_ops spec fctx =
  List.fold_right (fun elem spec -> add_fctx_elem_op spec elem)
                  fctx spec

(* Add all the axioms from a given fctx *)
let add_fctx_axioms spec fctx =
  List.fold_right (fun elem spec ->
                   add_axiom spec (fctx_elem_id elem) (fctx_elem_type elem))
                  fctx spec

(* Complete a spec, by creating its axiom type-class and giving it a
   global name; NOTE: this must be done *inside* the spec *)
let complete_spec spec spec_name =
  let _ = match spec.spec_name with
    | Some id -> anomaly (str "compete_spec: spec is already named!")
    | None -> ()
  in
  add_typeclass spec_name false
                (fctx_params spec.spec_op_ctx)
                (List.rev_map
                   (fun ax_name ->
                    (ax_name, mk_var (dummy_loc, axiom_type_id ax_name), false))
                   ax_fields);
  { spec with
    spec_name =
      Some (lookup_spec_globref (qualid_of_ident spec_name))}


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = ref (MPmap.empty)

(* Register a spec in the spec_table *)
let register_global_spec spec =
  let spec_name = match spec.spec_name with
    | Some n -> n
    | None -> anomaly (str "register_global_spec: anonymous spec!")
  in
  (*
  Format.eprintf "\nregister_global_spec: ind (name = %s, id = %i)\n"
                 (MutInd.to_string ind) i
   *)
  spec_table := MPmap.add spec_name spec !spec_table

(* Look up a spec and its spec_globref from a local spec reference *)
let lookup_spec_and_globref locref =
  let globref = lookup_spec_globref locref in
  (MPmap.find globref !spec_table, globref)

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
let resolve_name_translation spec xlate : name_subst =
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
 *** Spec Morphisms
 ***)

(* A morphism contains source and target specs, a name substitution
   mapping ops from the former to the latter, and a global reference
   to an interpretation function that builds an instance of the source
   spec's type-class from that of the target *)
type morphism = {
  morph_source : spec;
  morph_target : spec;
  morph_subst : name_subst;
  morph_interp : global_reference
}

(* The implicit argument name for the spec argument of a morphism
   interpretation function *)
let morph_spec_arg_id = Id.of_string "Spec"

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

(* An attempt to add a definition to an already-defined field *)
exception FieldAlreadyDefined of Id.t

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
            raise loc (FieldAlreadyDefined (fctx_elem_id elem))
          else ()
       | None -> ())
      removed_defs
  in

 FIXME HERE: use stable_reverse_topo_sort to add the new definitions

  within_module
    spec_id
    (fun () ->
     (* Start by adding all the target ops to the current spec *)
     let spec_t_ops = add_fctx_ops empty_spec
                                     morph.morph_target.spec_op_ctx
       in

       (* Iterate over the ops in spec, adding them if they are not in
          source and checking compatibility with source if they are *)
       let spec_all_ops =
         List.fold_right
           (fun elem spec ->
            match fctx_lookup morph.morph_source.spec_op_ctx
                              (fctx_elem_id elem) with
            | None ->
               (* Op is not in source, so add it *)
               add_fctx_elem_op spec elem
            | Some elem_s ->
               (* Op is in source, so don't add it; but do check if it
                  has the same type as in source *)
               if ~(check_equal_term (fctx_elem_type elem)
                                     (fctx_elem_type elem_s)) then
                 raise loc (FieldMismatch (fctx_elem_id elem, false))

               (* If op is defined in both spec and source, check that
                  the definitions are equal *)
               else if fctx_elem_is_def elem &&
                         fctx_elem_is_def elem_s &&
                           ~(check_equal_term (fctx_elem_def elem)
                                              (fctx_elem_def elem_s))
               then
                 raise loc (FieldMismatch (fctx_elem_id elem, false))

               (* If op is defined in spec and not in source, make
                  sure it does not become defined in target *)
               (* NOTE: a more permissive check would just require
                  target.op = spec.op *)
               else if fctx_elem_is_def elem &&
                         ~(fctx_elem_is_def elem_s) then
                 match fctx_lookup morph.morph_target.spec_op_ctx
                                   (subst_id morph.morph_subst
                                             (fctx_elem_id elem))
                 with
                 | Some elem_t ->
                    if fctx_elem_is_def elem_t then
                      raise loc (FieldAlreadyDefined (fctx_elem_id elem))
                    else
                      spec
                 | None -> spec
           )
           spec.spec_op_ctx spec_t_ops
       in

       (* Add all the axioms in target to the current spec *)
       let spec_t_axioms =
         add_fctx_axioms spec_all_ops morph.morph_target.spec_axioms in
       (* Add all the axioms in spec - source, making sure that any
          shared axioms have the same type *)
       let spec_all_axioms =
         add_fctx_axioms spec_t_axioms
                         (fctx_subtract
                            (fun elem elem_s ->
                             if ~(check_equal_term (fctx_elem_type elem)
                                                   (fctx_elem_type elem_s)) then
                               raise loc (FieldMismatch (fctx_elem_id, false))
                             else ()
                            )
                            spec.spec_axioms morph.morph_source.spec_axioms)
       in
       let spec = complete_spec spec_all_axioms spec_id in

       (* FIXME HERE: add derived instances! (maybe return them as well?) *)

       spec
      )
  in
  let _ = register_global_spec new_spec in
  (new_spec, qualid_of_ident spec_id)


(***
 *** Axiom Substitutions
 ***)

(*
(* An axiom substitution shows how to prove all the axioms of a source
   spec using axioms of a target spec, either by mapping them directly
   to axioms in the target spec or by mapping them to fields in an
   intermediate spec whose axioms are in turn mapped to the target *)
type ax_proof =
  | AxPf_Direct of Id.t (* Prove an axiom directly by another axiom *)
  | AxPf_Morph of int * Id.t (* Prove via a named axiom in the nth
                                morphism application (see below) *)
type simple_ax_subst = (Id.t * ax_proof) list

(* Represents the application of a named morphism whose ops and axioms
   are mapped to the target spec *)
type morph_appl =
    global_reference * name_subst * simple_ax_subst

(* A full axiom substitution contains the mappings and the morphism
   applications that are used in those mappings; note that as_morphs
   is reversed, in that earlier morphism applications can refer to
   later ones, but not vice-versa *)
type ax_subst = {as_morphs : morph_appl list; as_subst : simple_ax_subst }

(* The empty axiom substitution *)
let empty_ax_subst = ([], [])

(* Build the default morphism application from a morphism, that
   contains the identity map for all the ops and axioms in the target
   of the morphism (these are the args to the interpretation fun) *)
let morph_appl_from_morph morph =
  (morph.morph_interp,
   List.map (fun elem -> (op_ctx_elem_id elem, op_ctx_elem_id elem,
                          op_ctx_elem_is_def elem))
            morph.morph_target.spec_op_ctx;
   List.map (fun ax_id -> (ax_id, AxPf_Direct ax_id))
            morph.morph_target.spec_axioms)

(* Apply a name substitution to an ax_proof *)
let subst_ax_proof subst pf =
  match pf with
  | AxPf_Direct id -> AxPf_Direct (subst_id subst id)
  | _ -> pf (* Morphism numbers and field names in morphisms don't change *)

(* Apply a name substitution to a simple_ax_subst *)
let subst_ax_subst_simple subst ax_subst =
  List.map (fun (id, pf) -> (id, subst_ax_proof subst pf)) ax_subst

(* Apply a name substitution to a morph_appl *)
let subst_morph_appl subst (r, op_subst, ax_subst) =
  (r, subst_name_subst subst op_subst,
   subst_ax_subst_simple subst ax_subst)

(* Apply a name substitution to the RHS's of an axiom substitution *)
let subst_ax_subst subst ax_subst =
  {as_morphs = List.map (subst_morph_appl subst) ax_subst.as_morphs;
   as_subst = subst_ax_subst_simple subst ax_subst.as_subst}

(* Apply a morphism to an axiom proof, replacing any axiom on the RHS
   in the source spec with a reference to that axiom in morph_num *)
let apply_morphism_ax_proof morph morph_num pf =
  match pf with
  | AxPf_Direct id ->
     if List.exists ((=) id) morph.morph_source.spec_axioms then
       AxPf_Morph (morph_num, id)
     else pf
  | _ -> pf

(* Apply a morphism to a simple axiom substitution *)
let apply_morphism_ax_subst_simple morph morph_num ax_subst =
  List.map (fun (id, pf) ->
            (id, apply_morphism_ax_proof morph morph_num pf)) ax_subst

(* Apply a morphism to a morphism application *)
let apply_morphism_morph_appl morph morph_num (r, op_subst, ax_subst) =
  (r, subst_name_subst morph.morph_subst op_subst,
   apply_morphism_ax_subst_simple morph morph_num ax_subst)

(* Apply a morphism to an axiom substitution *)
let apply_morphism_ax_subst morph ax_subst =
  (* First, get the number for the morph_apply we are going to add (it
     is going to be the next one in the list) *)
  let morph_num = List.length ax_subst.ax_morphs in
  (* Now apply the morphism to the existing morphism applications and
     the simple axiom substitutions, and then append the new morphism
     application *)
  { as_morphs =
      List.map (apply_morphism_morph_appl morph morph_num) ax_subst.as_morphs
      @ [morph_appl_from_morph morph];
    as_subst = apply_morphism_ax_subst_simple morph morph_num ax_subst.as_subst }
 *)

(***
 *** Spec Imports and Spec Terms
 ***)

(*
(* An import morphism is a morphism where the interpretation function
   is determined by an axiom substitution with a list of intermediate
   morphism applications. The source of an import morphism is always
   given by name, while the target of an import morphism is is left
   implicit as it is always the current spec. *)
type import_morphism = {
  imorph_source : spec_locref;
  imorph_op_subst : name_subst;
  (* imorph_defs : (Id.t * name_subst * Constrexpr.constr_expr) list; *)
  imorph_ax_subst : ax_subst
}

(* Apply a name substitution to the defs of an import morphism *)
(*
let subst_imorph_defs subst defs =
  List.map (fun (id,subst,body) ->
            (subst_id subst id,
             subst_name_subst morph.morph_subst subst, body))
           defs
 *)

(* Apply a name substitution to an import morphism *)
let subst_import_morph subst imorph =
  { imorph with
    imorph_op_subst = subst_name_subst subst imorph.imorph_op_subst;
    (* imorph_defs = subst_imorph_defs subst imorph.imorph_defs; *)
    imorph_ax_subst = subst_ax_subst subst imorph.imorph_ax_subst }

(* Apply a morphism to an import morphism *)
let apply_morphism_imorph morph imorph =
  { imorph with
    imorph_op_subst =
      subst_name_subst morph.morph_subst imorph.imorph_op_subst;
    (* imorph_defs = subst_imorph_defs morph.morph_subst imorph.imorph_defs; *)
    imorph_ax_subst =
      apply_morphism_ax_subst morph imorph.imorph_ax_subst
  }

(* For each (name,body) pair in a list of definitions, change name to
   be defined in spec and also form the triple (name,op_ctx,body)
   where op_ctx is the op_ctx prefix before name in spec *)
(*
let rec add_spec_defs loc spec defs =
  let rec add_def op_ctx id body =
    let add_elem elem (op_ctx_ret, form) = (elem :: op_ctx_ret, form) in
    (* FIXME: error messages *)
    match op_ctx with
    | [] -> raise loc (Failure "Op not defined in spec")
    | (OpCtx_Decl id') as elem :: op_ctx' ->
       if id = id' then
         (OpCtx_Defn id' :: op_ctx',
          (id, op_ctx', body))
       else
         add_elem elem (add_def op_ctx' id body)
    | (OpCtx_Defn id') as elem :: op_ctx' ->
       if id = id' then
         raise loc (Failure "Op already defined in spec")
       else
         add_elem elem (add_def op_ctx' id body)
  in
  let rec add_defs_op_ctx op_ctx defs =
    match defs with
    | [] -> op_ctx
    | (id,body) :: defs' ->
       let add_form form (op_ctx_ret, forms) = (op_ctx_ret, form :: forms) in
       let (op_ctx',form) = add_def op_ctx id body in
       add_form form (add_defs_op_ctx op_ctx' defs')
  in
  let (op_ctx', forms) = add_defs_op_ctx spec.spec_op_ctx defs in
  ({ spec with spec_op_ctx = op_ctx' }, forms)
 *)
 *)

(* Spec terms are syntactic forms for building specs from existing
   specs; they are built from a "body" that modifies an existing,
   named spec via name translations and morphisms, along with a list
   of definitions that are supplied for declared ops in the spec *)
type spec_term_body =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * name_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * qualid located
  (* Adding definitions to ops in a spec *)
  (* | SpecAddDefs of spec_term * (Id.t * Constrexpr.constr_expr) list *)

type spec_term = spec_term_body * (Id.t * Constrexpr.constr_expr) list

(* Get the source location of a spec_term *)
let rec spec_term_loc st =
  match st with
  | SpecRef r -> loc_of_reference r
  | SpecXlate (st', _) -> spec_term_loc st'
  | SpecSubst (st', _) -> spec_term_loc st'
  (* | SpecAddDefs (st', _) -> spec_term_loc st' *)

(* Interpret a spec term into a spec plus an import morphism to that
   spec from the base spec (the SpecRef) of the spec term *)
(*
let rec interp_spec_term_body sterm : spec * import_morphism =
  match sterm with
  | SpecRef r ->
     (try
         let locref = spec_locref_of_ref r in
         (lookup_spec locref,
          {imorph_source = locref; imorph_op_subst = [];
           imorph_ax_subst = empty_ax_subst })
       with Not_found ->
         user_err_loc (spec_term_loc sterm, "_",
                       str ("No spec named " ^ string_of_reference r)))
  | SpecXlate (sterm', xlate) ->
     let (spec, imorph) = interp_spec_term_body sterm' in
     let subst = resolve_name_translation spec xlate in
     (subst_spec subst spec, subst_import_morph subst imorph)
  | SpecSubst (sterm', morph_ref) ->
     let (spec, imorph) = interp_spec_term_body sterm' in
     let morph = lookup_morphsim (located_elem morph_ref) in
     (apply_morphism (located_loc morph_ref) morph spec,
      apply_morphism_imorph morph imorph)
(*
  | SpecAddDefs (sterm', defs) ->
     let (spec, imorph) = interp_spec_term sterm' in
     let (new_spec, new_defs) = add_spec_defs spec defs in
     (new_spec,
      {imorph with
        imorph_defs = (List.map (fun (id,op_ctx,body) ->
                                 (id, subst_from_op_ctx op_ctx, body))
                                new_defs) @ imorph.imorph_defs})
 *)
 *)


(* Import a spec at the given locref while applying the given optional
   name translation and adding the given definitions *)
let import_spec_with_changes spec im_spec im_ref xlate_opt defs =
  

(* Global counter for making fresh local spec names *)
let import_counter = ref 1

(* Get a fresh local spec name *)
let fresh_import_id () =
  let n = !import_counter in
  let _ = import_counter := n+1 in
  Id.of_string ("import__" ^ string_of_int n)

(* Interpret a spec term and import it into spec, which is assumed to
   be the current spec (as local definitions are created) *)
let rec import_spec_term spec (body,defs) =

  (* Make a fresh, empty spec and import sterm_body into it *)
  let import_into_fresh_spec sterm_body =
    let spec_name = fresh_import_id () in
    let spec =
      within_module
        spec_name
        (fun () -> import_spec_term empty_spec (sterm_body, [])) in
    (spec, spec_name)
  in

  (* FIXME HERE *)
  let import_spec spec im_spec im_locref xlate_opt defs =
    FIXME HERE
  in

  let rec import_aux spec body xlate_opt defs =
    match body with
    | SpecRef r ->
       (try
           let locref = spec_locref_of_ref r in
           (lookup_spec locref, locref)
         with Not_found ->
           user_err_loc (spec_term_loc sterm, "_",
                         str ("No spec named " ^ string_of_reference r)))
    | _ -> FIXME HERE
  in
  import_aux spec body None defs

     (* Interpret a spec term and then import the resulting spec into the
   current spec *)
let import_spec_term spec (sterm, defs) =
  let (im_spec, imorph) = interp_spec_term_body sterm in
  

  FIXME HERE


(***
 *** The data-types for specifying specs (ha ha)
 ***)

(* A spec def entry is an op, axiom, or import in a spec definition *)
type spec_def_entry =
  (* Declaration of an op: contains its name and type *)
  | OpEntry of lident * Constrexpr.constr_expr
  (* Definition of an op: contains its name, type, and value *)
  | OpDefEntry of lident * Constrexpr.constr_expr option * Constrexpr.constr_expr
  (* Declaration of an axiom: contains its name and type *)
  | AxEntry of lident * Constrexpr.constr_expr
  (* Import of another spec: contains the spec name and a list of
    "with clauses" that define some declared ops of that spec *)
  | ImportEntry of spec_term


(***
 *** Interpreting specs into type-classes
 ***)

(* Interpret a spec term (which for now is just a name) into a spec
   and a local reference to that spec *)
(* FIXME HERE: should be import_spec_term *)
let rec interp_spec_term sterm : spec * spec_locref =
  match sterm with
  | SpecRef ref ->
     (try
         let locref = spec_locref_of_ref ref in
         (lookup_spec locref, locref)
       with Not_found ->
            raise (spec_term_loc sterm)
                  (Failure ("No spec named " ^ string_of_reference ref)))
  | SpecXlate (sterm', nmap) ->
     raise (spec_term_loc sterm) (Failure "interp_spec_term")
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst (sterm', morph_name) ->
     raise (spec_term_loc sterm) (Failure "interp_spec_term")
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs (sterm', defs) ->
     raise (spec_term_loc sterm) (Failure "interp_spec_term")

(* Interpret a list of spec_entries into a spec object, installing a
   series of typeclasses and definitions into the current Coq
   image. Also takes in an op_ctx of the ops that have been added so
   far and the current list of fields, in reverse order, to go into
   the axiom typeclass *)
let rec interp_spec_def_entries spec_name op_ctx ax_fields entries =
  match entries with
  | [] ->
     (* At the end of all entries, make the final, propositional
        type-class for all the axioms and imports, and return the spec
        object *)
     add_typeclass spec_name false
                   (fctx_params op_ctx) (List.rev ax_fields) ;
     { spec_ops = op_ctx;
       spec_axioms = List.map (fun (lid,_,_) -> located_elem lid) ax_fields
     }
  | OpEntry (op_name, op_type) :: entries' ->
(*
  | GallinaEntry (VernacAssumption ((_, Definitional), NoInline,
                                    [false, ([op_name], op_type)]))
    :: entries' ->
 *)
     (* For an op declaration, make an operational typeclass
        Class op__class {op_params} := { op : op_type }
      *)
     add_typeclass (add_suffix_l op_name "class") true
                   (fctx_params op_ctx)
                   [(op_name, op_type, false)] ;
     interp_spec_def_entries spec_name (op_ctx_cons_decl op_name op_ctx)
                         ax_fields entries'
  | OpDefEntry (op_name, op_type_opt, op_body) :: entries' ->
(*
  | GallinaEntry (VernacDefinition
                    ((_, Definition), op_name,
                     DefineBody (old_params, None, op_body, op_type_opt)))
    :: entries' ->
 *)
     (* For an op definition, add the forms

        Definition op {op_params} : op_type := op_body
        Class op__class {op_params} := { op__def : op_type }

        and add the axiom op__eq : op__def = op
      *)
     let op_type =
       match op_type_opt with
       | Some op_type -> op_type
       | None -> CHole (located_loc op_name, None,
                        IntroIdentifier (located_elem op_name), None)
     in
(*
     let params = fctx_params op_ctx @ old_params in
 *)
     let params = fctx_params op_ctx in
     let op_def_id = add_suffix_l op_name "def" in
     add_definition op_name (fctx_params op_ctx) op_type_opt op_body ;
     add_typeclass (add_suffix_l op_name "class") true params
                   [(op_def_id, op_type, false)] ;
     interp_spec_def_entries spec_name (op_ctx_cons_defn op_name op_ctx)
                         (((add_suffix_l op_name "eq"),
                           (mk_ident_equality op_def_id op_name),
                           false)
                          :: ax_fields)
                         entries'
  | AxEntry (ax_name, ax_type) :: entries' ->
(*
  | GallinaEntry (VernacAssumption ((_, Logical), NoInline,
                                    [false, ([ax_name], ax_type)]))
    :: entries' ->
 *)
     (* For axioms, just make a record field for the final,
        propositional type-class and pass it forward *)
     interp_spec_def_entries spec_name op_ctx
                             ((ax_name, ax_type, false) :: ax_fields)
                             entries'
(*
  | GallinaEntry (gallina_cmd) :: _ ->
     raise (located_loc spec_name) (Failure "Unhandled form in spec")
 *)
  | ImportEntry sterm :: entries' ->
     let (im_spec, im_spec_ref) = interp_spec_term sterm in
     interp_spec_def_entries spec_name
                             (op_ctx_cons_import im_spec_ref im_spec op_ctx)
                             (((dummy_loc, im_spec_ref.ax_class_name),
                               mk_var (dummy_loc, im_spec_ref.ax_class_name), true)
                              :: ax_fields)
                             entries'


(* Top-level entrypoint to interpret a spec expression *)
let interp_spec_def spec_name entries =
  within_module spec_name
                (fun () ->
                 let spec = interp_spec_def_entries spec_name [] [] entries in
                 register_global_spec spec_name spec)
;;


(***
 *** Additions to the Coq parser
 ***)

(* FIXME: get the locations of all the identifiers right! *)

(* Syntactic class to parse import defs *)
VERNAC ARGUMENT EXTEND import_defs
  | [ ident(nm) ":=" constr(def) ";" import_defs(rest) ] -> [ (nm, def)::rest ]
  | [ ident(nm) ":=" constr(def) ] -> [ [nm, def] ]
END

(* New syntactic class to parse individual spec entries *)
VERNAC ARGUMENT EXTEND spec_def_entry
  | [ "Variable" ident(nm) ":" constr(tp) ] -> [ OpEntry ((loc, nm), tp) ]
  | [ "Definition" ident(nm) ":" constr(tp) ":=" constr(body) ] -> [ OpDefEntry ((loc, nm), Some tp, body) ]
  | [ "Definition" ident(nm) ":=" constr(body) ] -> [ OpDefEntry ((loc, nm), None, body) ]
  | [ "Axiom" ident(nm) ":" constr(tp) ] -> [ AxEntry ((loc, nm), tp) ]
  | [ "Import" global(spec_term) ] -> [ ImportEntry (SpecRef spec_term) ]
END

type spec_entries = spec_def_entry list

(* New syntactic class to parse lists of one or more spec entries,
   separated by semicolons *)
VERNAC ARGUMENT EXTEND spec_entries
  | [ spec_def_entry(entry) ";" spec_entries(rest) ] -> [ entry::rest ]
  | [ spec_def_entry(entry) ] -> [ [entry] ]
END

(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec
  | [ "Spec" ident(spec_name) "{" spec_entries(entries) "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ interp_spec_def (dummy_loc, spec_name) entries ]
  | [ "Spec" ident(spec_name) "{" "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ interp_spec_def (dummy_loc, spec_name) [] ]
END
