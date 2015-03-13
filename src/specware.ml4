
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
 *** Helper functions for interacting with Coq
 ***)

(* Useful list function *)
let rec filter_map f l =
  match l with
  | [] -> []
  | x :: l' ->
     if f x then
       x :: filter_map f l'
     else
       filter_map f l'

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

(* Append a suffix to an Id, with "__" in between *)
let add_suffix id suffix =
  Id.of_string (Id.to_string id ^ "__" ^ suffix)

(* Append a suffix to an lident, with "__" in between *)
let add_suffix_l lid suffix =
  let (loc, id) = lid in
  (loc, add_suffix id suffix)

(* Build an expression for a variable from a located identifier *)
let mk_var id = CRef (Libnames.Ident id, None)

(* Build an expression for a variable applied to named implicit args,
   where the args are given as (name,value) pairs *)
let mk_var_app_named_args id args =
  CApp (dummy_loc,
        (None, CRef (Libnames.Ident id, None)),
        List.map (fun (id,arg) ->
                  (arg, Some (dummy_loc, ExplByName id))) args)

(* Build a qualified id *)
let mk_qualid dir id =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) id

(* Cons an id onto the end of a qualid *)
let qualid_cons qualid id =
  let (mod_path,mod_name) = repr_qualid qualid in
  make_qualid (DirPath.make (DirPath.repr mod_path @ [mod_name])) id

(* Build the expression id1 = id2 for identifiers id1 and id2 *)
let mk_ident_equality id1 id2 =
  let loc = located_loc id1 in
  CApp (loc,
        (None,
         CRef (Qualid (loc, mk_qualid ["Coq"; "Init"; "Logic"] (Id.of_string "eq")),
               None)),
        [(mk_var id1, None); (mk_var id2, None)])

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

(***
 *** Global and local references to specs
 ***)

(* FIXME: figure out how to get good error messages in the lookup
   functions! *)

(* A local reference to a spec is a name for the spec that is relative
   to the current module, section, etc. Local spec references contain
   local references (qualified identifiers) to the module where the
   spec is defined, as well the names of the op and axiom
   typeclasses inside that module. *)
type spec_locref = { spec_module_qualid : qualid;
                     op_class_name : Id.t;
                     ax_class_name : Id.t;
                     spec_locref_loc : Loc.t }

(* Build a spec_locref from a local reference to a spec's module,
   which is the user-visible way to name specs *)
let spec_locref_of_ref ref =
  let mod_qualid = located_elem (qualid_of_reference ref) in
  let (_,mod_name) = repr_qualid mod_qualid in
  { spec_module_qualid = mod_qualid;
    op_class_name = add_suffix mod_name "ops";
    ax_class_name = mod_name;
    spec_locref_loc = loc_of_reference ref }

(* Return a qualid for the op class of a spec given a spec_locref *)
let op_class_qualid spec_locref =
  qualid_cons spec_locref.spec_module_qualid spec_locref.op_class_name

(* Return a qualid for the axiom class of a spec given a spec_locref *)
let ax_class_qualid spec_locref =
  qualid_cons spec_locref.spec_module_qualid spec_locref.ax_class_name

(* A global reference to a spec is a global reference to the axiom
   typeclass of the spec, which is a Coq inductive object *)
type spec_globref = MutInd.t

(* Lookup the global reference to a spec from a local reference *)
(* FIXME: make better error messages! *)
let lookup_spec_globref locref =
  match Nametab.locate (ax_class_qualid locref) with
  | Globnames.IndRef (ind, i) -> ind
  | _ -> raise (locref.spec_locref_loc) (Failure "Does not refer to a spec")

(* FIXME: figure out how to print constrs to strings *)
(* Turn a global spec name into a string, for printing *)
(*
let spec_globref_to_string spec_ref =
  (printable_constr_of_global spec_ref)
 *)

(* Turn the global reference to a spec into a local qualid *)
(* FIXME: find a better way than going through strings... *)
let spec_globref_to_qualid spec_globref =
  qualid_of_string (MutInd.to_string spec_globref)


(***
 *** Op Contexts
 ***)

(* An op context specifies the ops that are currently in scope, and,
   for each op, whether it is defined or just declared.

   NOTE: op contexts always have the most recently declared or defined
   op first, i.e., the first op in a spec is the last op in an op
   context; this is to make it easy to append ops as we go *)
type op_ctx_elem =
  | OpCtx_Decl of Id.t
  | OpCtx_Defn of Id.t

type op_ctx = op_ctx_elem list

(* Get the identifier for an op_ctx_elem *)
let op_ctx_elem_id op_ctx_elem =
  match op_ctx_elem with
  | OpCtx_Decl id -> id
  | OpCtx_Defn id -> id

(* Return true iff an op_cxt_elem is a definition *)
let op_ctx_elem_is_def op_ctx_elem =
  match op_ctx_elem with
  | OpCtx_Decl _ -> false
  | OpCtx_Defn _ -> true

(* Get the identifier for the variable bound to an op_ctx_elem in an
   implicit argument list *)
let op_ctx_elem_var_id op_ctx_elem =
  add_suffix (op_ctx_elem_id op_ctx_elem) "param"

(* Get the identifier for the type-class of an op_ctx_elem *)
let op_ctx_elem_class_id op_ctx_elem =
  add_suffix (op_ctx_elem_id op_ctx_elem) "class"

(* Build a term for the type-class of the identifier for the parameter
   name of an op_ctx_elem *)
let op_ctx_elem_class op_ctx_elem =
  mk_var (Loc.dummy_loc, op_ctx_elem_class_id op_ctx_elem)

(* Get the field names represented by an op_ctx *)
(*
let rec op_ctx_fields op_ctx =
  match op_ctx with
  | [] -> []
  | OpCtx_Decl id :: op_ctx' ->
     id :: op_ctx_fields op_ctx'
  | OpCtx_Defn id :: op_ctx' ->
     id :: op_ctx_fields op_ctx'
  | OpCtx_Import (locref, shared_fields, im_op_ctx) :: op_ctx' ->
     op_ctx_fields im_op_ctx @ (locref.ax_class_name :: op_ctx_fields op_ctx')
 *)

(* Subtract the fields of op_ctx2 from op_ctx *)
(* FIXME: should check that fields being subtracted are compatible *)
let rec op_ctx_sub op_ctx op_ctx2 =
  filter_map
    (fun elem ->
     not (List.exists
            (fun elem2 -> op_ctx_elem_id elem = op_ctx_elem_id elem2)
            op_ctx2))
    op_ctx

(* Cons an op declaration to an op_ctx *)
let op_ctx_cons_decl op_name op_ctx =
  OpCtx_Decl (located_elem op_name) :: op_ctx

(* Cons an op definition to an op_ctx *)
let op_ctx_cons_defn op_name op_ctx =
  OpCtx_Defn (located_elem op_name) :: op_ctx

(* Cons an import to an op_ctx *)
(*
let op_ctx_cons_import spec_locref spec op_ctx =
  (* Get the list of fields in the current op_ctx *)
  let fields = op_ctx_fields op_ctx in
  (* Get the sub-list of fields in spec that are in the current context *)
  let shared_fields = List.filter (fun id -> List.mem id fields)
                                  (op_ctx_fields spec.spec_ops) in
  OpCtx_Import (spec_locref, shared_fields,
                op_ctx_subtract_fields spec.spec_ops shared_fields) :: op_ctx
 *)

(* Convert a single op_ctx_elem to an implicit class assumption *)
let op_ctx_to_param op_ctx_elem =
  mk_implicit_assum (op_ctx_elem_var_id op_ctx_elem)
                    (op_ctx_elem_class op_ctx_elem)

(* Convert an op_ctx to a list of class parameters, one for each op in
   the context (remember: op_ctx is reversed, so we fold left instead
   of right) *)
let op_ctx_to_params op_ctx =
  List.rev_map op_ctx_to_param op_ctx
(*
let rec op_ctx_to_params op_ctx =
  List.fold_left
    (fun params elem ->
     match elem with
     | OpCtx_Decl id ->
        mk_implicit_assum
          (add_suffix id "param")
          (mk_var (Loc.dummy_loc, add_suffix id "class"))
        :: params
     | OpCtx_Defn id ->
        mk_implicit_assum
          (add_suffix id "param")
          (mk_var (Loc.dummy_loc, add_suffix id "class"))
        :: params
     | OpCtx_Import (_, im_id, shared_fields, im_op_ctx) ->
        op_ctx_to_params im_op_ctx
        @ (mk_var_app_named_args
             (Loc.dummy_loc, add_suffix im_id "ops")
             (List.map (fun id ->
                        (add_suffix id "param",
                         mk_var (dummy_loc, add_suffix id "param")))
                       shared_fields)
           :: params))
    [] op_ctx
 *)


(***
 *** The internal representation of specs
 ***)

(* A spec is represented internally as having an optional global name
   (specs without names are called "anonymous", and are only for
   temporary calculations), an op context (giving the names of the ops
   it declares and/or defines), and a list of axiom names. Note that
   we do not store the types or values of ops and axioms, relying on
   Coq's other definition mechanisms for that. *)
type spec = {
  spec_name : spec_globref option;
  spec_op_ctx : op_ctx;
  spec_axioms : Id.t list
}

(* Convert an axiom id to the id of the defined variable holding its type *)
let axiom_type_id ax_id =
  add_suffix ax_id "prop"

(* Subtract a list of axioms from another list of axioms *)
(* FIXME: check that any overlapping axioms have compatible types *)
let axioms_sub axioms1 axioms2 =
  filter_map
    (fun id1 ->
     not (List.exists (fun id2 -> id1 = id2) axioms2))
    axioms1

(* Create an anonymous empty spec *)
let empty_spec = { spec_name = None; spec_op_ctx = []; spec_axioms = [] }

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to a spec, creating a type-class for it *)
let add_declared_op spec op_name op_type =
  let elem = OpCtx_Decl (located_elem op_name) in
  add_typeclass
    (located_loc op_name, op_ctx_elem_class_id elem)
    true (op_ctx_to_params spec.spec_op_ctx)
    [(op_name, op_type, false)] ;
  { spec with spec_op_ctx = elem :: spec.spec_op_ctx }

(* Add an axiom to a spec, creating a definition for its type *)
let add_axiom spec ax_name ax_type =
  let ax_id = located_elem ax_name in
  add_definition (located_loc ax_name, axiom_type_id ax_id)
                 (op_ctx_params spec.spec_op_ctx)
                 prop_expr ax_type ;
  { spec with spec_axioms = ax_id :: spec.spec_axioms }

(* Add a defined op to a spec, creating a type-class and def for it *)
let add_defined_op spec op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let elem = OpCtx_Defn op_id in
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let params = op_ctx_to_params spec.spec_op_ctx in
  let op_var_id = add_suffix_l op_name "var" in

  (* Add a definition op_name = op_body *)
  add_definition op_name params op_type_opt op_body ;

  (* Add a type-class for op_name__var : op_type *)
  add_typeclass (op_ctx_elem_class_name elem) true params
                [(op_var_id, op_type, false)] ;

  (* Add an axiom "op_name = op_name__var" to the resulting spec *)
  add_axiom
    { spec with spec_op_ctx = elem :: spec.spec_op_ctx }
    (add_suffix_l op_name "eq")
    (mk_ident_equality op_var_id op_name)


(* Create the axiom type-class for a spec *)
let add_axiom_typeclass spec =
  let spec_name = match spec.spec_name with
    | Some id -> id
    | None -> anomaly (str "add_axiom_typeclass: anonymous spec!")
  in
  add_typeclass spec_name false
                (op_ctx_to_params spec.spec_op_ctx)
                (List.rev_map
                   (fun ax_name ->
                    (ax_name, mk_var (dummy_loc, axiom_type_id ax_name), false))
                   ax_fields)


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = ref (Mindmap.empty)

(* Register a spec in the spec_table given a local id that refers to
   the axiom class in the spec *)
let register_global_spec spec_lident spec =
  let spec_globref = lookup_spec_globref
                       (spec_locref_of_ref (Ident spec_lident)) in
  (*
  Format.eprintf "\nregister_global_spec: ind (name = %s, id = %i)\n"
                 (MutInd.to_string ind) i
   *)
  spec_table := Mindmap.add spec_globref spec !spec_table

(* Look up a spec and its spec_globref from a local spec reference *)
let lookup_spec_and_globref locref =
  let globref = lookup_spec_globref locref in
  (Mindmap.find globref !spec_table, globref)

(* Look up a spec from a local spec reference *)
let lookup_spec locref = fst (lookup_spec_and_globref locref)


(***
 *** Name Substitutions and Name Translations
 ***)

(* A name substitution is a finite mapping on identifiers, with an
   additional flag stating whether the source is a defined op *)
type name_subst = (Id.t * Id.t * bool) list

(* Apply a name substitution to a name *)
let rec subst_id subst id =
  match subst with
  | [] -> id
  | (id_from, id_to, _) :: subst' ->
     if id_from = id then id_to else subst_id subst' id

(* Apply name substitution subst to all the names in the range of
   another name substitution subst2 *)
let rec subst_name_subst subst subst2 =
  match subst2 with
  | [] -> []
  | (id_from, id_to, flag) :: subst2' ->
     (id_from, subst_id subst id_to, flag)
     :: subst_name_subst subst subst2'

(* Apply a name substitution to an op_ctx_elem *)
let subst_op_ctx_elem subst elem =
  match elem with
  | OpCtx_Decl id -> OpCtx_Decl (subst_id id)
  | OpCtx_Defn id -> OpCtx_Defn (subst_id id)

(* Apply a name substitution to an op_ctx *)
let subst_op_ctx subst op_ctx =
  List.map subst_op_ctx_elem op_ctx

(* Apply a name substitution to a spec *)
let subst_spec subst spec =
  { spec_op_ctx = subst_op_ctx subst spec.spec_op_ctx;
    spec_axioms = List.map (subst_id subst) spec.spec_axioms }

(* Build the identity substitution for an op_ctx *)
let subst_from_op_ctx op_ctx =
  List.map (fun elem -> (op_ctx_elem_id elem, op_ctx_elem_id elem,
                         op_ctx_elem_is_def elem)) op_ctx

(* A name translation specifies a name substitution, e.g., with patterns *)
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

(* Instantiate a name translation into a finite name substitution for
   a particular spec *)
let interp_name_translation spec xlate : name_subst =
  let rec helper elem_fun l =
    match l with
    | [] -> []
    | elem :: l' ->
       let (id,flag) = elem_fun elem in
       let rest = helper elem_fun l' in
       (match translate_id xlate id with
        | Some id' ->
           if op_ctx_elem_is_def elem then
             (* If id is a def, also map id__eq -> id'__eq *)
             (id, id', flag) ::
               (add_suffix id "eq", add_suffix id "eq", flag) :: rest
           else
             (id, id', flag) :: rest
        | None -> rest)
  in
  helper (fun elem -> (op_ctx_elem_id elem,
                       op_ctx_elem_is_def elem)) spec.spec_op_ctx
  @ helper (fun id -> (id, false)) spec.spec_axioms


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

(* Apply morph to spec, yielding (target ++ (spec - source)); i.e.,
   remove any ops and axioms listed in the source spec and then
   prepend the target spec.  The loc is for any error messages; e.g.,
   if an op or axiom is shared between spec and source but has
   different types in these two specs, or if an op or axiom is shared
   between (spec - source) and target but has different types in these
   two specs. *)
(* FIXME: figure out how to check these conditions! *)
let apply_morphism loc morph spec =
  { spec_name = None;
    spec_op_ctx = morph.morph_target.spec_op_ctx
                  @ op_ctx_sub spec.spec_op_ctx
                               morph.morph_source.spec_op_ctx;
    spec_axioms = morph.morph_target.spec_axioms
                  @ (axioms_sub spec.spec_axioms
                                morph.morph_source.spec_axioms) }

(* The implicit argument name for the spec argument of a morphism
   interpretation function *)
let morph_spec_arg_id = Id.of_string "Spec"

(* FIXME HERE: make a function that sets up the proof obligations for
   a morphism, and then adds it to a global morphism table when
   finished *)
(* let start_morphism morph_name xlate *)


(***
 *** Axiom Substitutions
 ***)

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


(***
 *** Spec Imports and Spec Terms
 ***)

(* An import morphism is a morphism where the interpretation function
   is determined by an axiom substitution with a list of intermediate
   morphism applications. Also, an import morphism can add definitions
   to ops that were undefined in the base spec. The source of an
   import morphism is always given by name, while the target of an
   import morphism is is left implicit as it is always the current spec. *)
type import_morphism = {
  imorph_source : spec_locref;
  imorph_op_subst : name_subst;
  imorph_defs : (Id.t * name_subst * Constrexpr.constr_expr) list;
  imorph_ax_subst : ax_subst
}

(* Apply a name substitution to the defs of an import morphism *)
let subst_imorph_defs subst defs =
  List.map (fun (id,subst,body) ->
            (subst_id subst id,
             subst_name_subst morph.morph_subst subst, body))
           defs

(* Apply a name substitution to an import morphism *)
let subst_import_morph subst imorph =
  { imorph with
    imorph_op_subst = subst_name_subst subst imorph.imorph_op_subst;
    imorph_defs = subst_imorph_defs subst imorph.imorph_defs;
    imorph_ax_subst = subst_ax_subst subst imorph.imorph_ax_subst }

(* Apply a morphism to an import morphism *)
let apply_morphism_imorph morph imorph =
  { imorph with
    imorph_op_subst =
      subst_name_subst morph.morph_subst imorph.imorph_op_subst;
    imorph_defs = subst_imorph_defs morph.morph_subst imorph.imorph_defs;
    imorph_ax_subst =
      apply_morphism_ax_subst morph imorph.imorph_ax_subst
  }

(* For each (name,body) pair in a list of definitions, change name to
   be defined in spec and also form the triple (name,op_ctx,body)
   where op_ctx is the op_ctx prefix before name in spec *)
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

(* Spec terms are syntactic forms for building specs from existing specs *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * name_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * qualid located
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs of spec_term * (Id.t * Constrexpr.constr_expr) list

(* Get the source location of a spec_term *)
let rec spec_term_loc st =
  match st with
  | SpecRef r -> loc_of_reference r
  | SpecXlate (st', _) -> spec_term_loc st'
  | SpecSubst (st', _) -> spec_term_loc st'
  | SpecAddDefs (st', _) -> spec_term_loc st'

(* Interpret a spec term into a spec plus an import morphism to that
   spec from the base spec (the SpecRef) of the spec term *)
let rec interp_spec_term sterm : spec * import_morphism =
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
     let (spec, imorph) = interp_spec_term sterm' in
     let subst = interp_name_translation spec xlate in
     (subst_spec subst spec, subst_import_morph subst imorph)
  | SpecSubst (sterm', morph_ref) ->
     let (spec, imorph) = interp_spec_term sterm' in
     let morph = lookup_morphsim (located_elem morph_ref) in
     (apply_morphism (located_loc morph_ref) morph spec,
      apply_morphism_imorph morph imorph)
  | SpecAddDefs (sterm', defs) ->
     let (spec, imorph) = interp_spec_term sterm' in
     let (new_spec, new_defs) = add_spec_defs spec defs in
     (new_spec,
      {imorph with
        imorph_defs = (List.map (fun (id,op_ctx,body) ->
                                 (id, subst_from_op_ctx op_ctx, body))
                                new_defs) @ imorph.imorph_defs})

(* Interpret a spec term and then import the resulting spec into the
   current spec *)
let import_spec_term spec sterm =
  FIXME HERE: 


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
                   (op_ctx_to_params op_ctx) (List.rev ax_fields) ;
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
                   (op_ctx_to_params op_ctx)
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
     let params = op_ctx_to_params op_ctx @ old_params in
 *)
     let params = op_ctx_to_params op_ctx in
     let op_def_id = add_suffix_l op_name "def" in
     add_definition op_name (op_ctx_to_params op_ctx) op_type_opt op_body ;
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
