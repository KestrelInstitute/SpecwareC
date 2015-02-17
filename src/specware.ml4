
DECLARE PLUGIN "specware"

open Names
open Loc
open Libnames
open Pp
open Vernacexpr
open Vernacentries
open Constrexpr
open Misctypes
open Decl_kinds


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

(* Append a suffix to an Id, with "__" in between *)
let add_suffix id suffix =
  Id.of_string (Id.to_string id ^ "__" ^ suffix)

(* Append a suffix to an lident, with "__" in between *)
let add_suffix_l lid suffix =
  let (loc, id) = lid in
  (loc, add_suffix id suffix)

(* Build an expression for a variable from a located identifier *)
let mk_var id = CRef (Libnames.Ident id, None)

(* Build a qualified id *)
let mk_qual_id dir id =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) id

(* Build the expression id1 = id2 for identifiers id1 and id2 *)
let mk_ident_equality id1 id2 =
  let loc = located_loc id1 in
  CApp (loc,
        (None,
         CRef (Qualid (loc, mk_qual_id ["Coq"; "Init"; "Logic"] (Id.of_string "eq")),
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
                     ax_class_name : Id.t }

(* Build a spec_locref from a local reference to a spec's module,
   which is the user-visible way to name specs *)
let spec_locref_of_ref ref =
  let mod_qualid = located_elem (qualid_of_reference ref) in
  let (_,mod_name) = repr_qualid mod_qualid in
  { spec_module_qualid = mod_qualid;
    op_class_name = add_suffix mod_name "ops";
    ax_class_name = mod_name }

(* Return a qualid for the op class of a spec given a spec_locref *)
let op_class_qualid spec_locref =
  let (mod_path,mod_name) = repr_qualid spec_locref.spec_module_qualid in
  make_qualid (DirPath.make (DirPath.repr mod_path @ [mod_name]))
              spec_locref.op_class_name

(* Return a qualid for the axiom class of a spec given a spec_locref *)
let ax_class_qualid spec_locref =
  let (mod_path,mod_name) = repr_qualid spec_locref.spec_module_qualid in
  make_qualid (DirPath.make (DirPath.repr mod_path @ [mod_name]))
              spec_locref.ax_class_name

(* A global reference to a spec is a global reference to the axiom
   typeclass of the spec, which is a Coq inductive object *)
type spec_globref = MutInd.t

(* Lookup the global reference for a spec given a local reference to
   its axiom class. *)
(* FIXME: make better error messages! *)
let lookup_spec_globref ref =
  match Nametab.locate (located_elem (qualid_of_reference ref)) with
  | Globnames.IndRef (ind, i) -> ind
  | _ -> raise (loc_of_reference ref) (Failure "Does not refer to a spec")

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
 *** The data-types for specifying specs (ha ha)
 ***)

(* A name mapping specifies a mapping on identifiers *)
type name_mapping_elem =
  (* Map a single name to another *)
  | NameXSingle of Id.t * Id.t
  (* Map all names with a given prefix to instead use a different prefix *)
  | NameXPrefix of string * string

type name_mapping = name_mapping_elem list

(* Spec terms are syntactic forms for building specs from existing specs *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * name_mapping
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * qualid
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs of spec_term * (Id.t * Constrexpr.constr_expr) list

(* Get the source location of a spec_term *)
let rec spec_term_loc st =
  match st with
  | SpecRef r -> loc_of_reference r
  | SpecXlate (st', _) -> spec_term_loc st'
  | SpecSubst (st', _) -> spec_term_loc st'
  | SpecAddDefs (st', _) -> spec_term_loc st'

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

(* FIXME HERE: need to figure out how to parse top-level Gallina
   commands in order to use this alternate version of spec_def_entry *)

(* The syntactic representation (parsed but not yet type-checked) of a
   single spec entry, i.e., a single element of a spec. This is either
   a normal Gallina top-level command (though only certain ones are
   allowed), or is a spec import form *)
(*
type spec_def_entry =
  | GallinaEntry of vernac_expr
  (* Import of another spec: contains the spec name and a list of
    "with clauses" that define some declared ops of that spec *)
  | ImportEntry of lident * (Id.t * constr_expr) list
 *)


(***
 *** The internal representation of a spec
 ***)

(* An op context specifies the ops that are currently in scope, and,
   for each op, whether it is defined or just declared. It also
   includes all the spec imports of a spec. Note that any ops that
   come from an included spec are not listed at the top level of an
   op_ctx, but are instead captured in the import form in the op_ctx.

   NOTE: op contexts always have the most recently declared or defined
   op first, i.e., the first op in a spec is the last op in an op
   context; this is to make it easy to append ops as we go *)
type op_ctx_elem =
  | OpCtx_Decl of Id.t
  | OpCtx_Defn of Id.t
  (* Imports are specified by the local name of the imported spec
     (usually the last identifier in the path to the module of the
     spec), a global reference to the spec, the names of any ops in
     the imported spec that are shared with the current spec (i.e.,
     the ops from the spec that are already in the current op_ctx),
     and the imported spec's op_ctx minus any of the shared ops *)
  | OpCtx_Import of Id.t * spec_globref * Id.t list * op_ctx
 and op_ctx = op_ctx_elem list

(* FIXME HERE: do imports need global refs? If so, all specs need to
   have a global ref! *)

(* Get the identifier from an op_ctx_elem *)
let op_ctx_elem_id op_ctx_elem =
  match op_ctx_elem with
  | OpCtx_Decl id -> id
  | OpCtx_Defn id -> id
  | OpCtx_Import (id, _, _, _) -> id

(* Cons an op declaration to an op_ctx *)
let op_ctx_cons_decl op_name op_ctx =
  OpCtx_Decl (located_elem op_name) :: op_ctx

(* Cons an op definition to an op_ctx *)
let op_ctx_cons_defn op_name op_ctx =
  OpCtx_Defn (located_elem op_name) :: op_ctx

(* Convert an op_ctx_elem to a class parameter of the form
   {op__param:op__class} *)
let op_ctx_elem_to_param elem =
  let id = op_ctx_elem_id elem in
  LocalRawAssum ([(Loc.dummy_loc, Name (add_suffix id "param"))],
                 Default Implicit,
                 mk_var (Loc.dummy_loc, add_suffix id "class"))

(* Convert an op_ctx to a list of class parameters, one for each
   OpCtx_Decl in the context (remember: op_ctx is reversed) *)
let op_ctx_to_params op_ctx =
  List.rev_map op_ctx_elem_to_param op_ctx

(* A spec is represented internally as a global name, an op context
   (giving the names of the ops it declares and/or defines), and a
   list of axiom names. Note that we do not store the types and/or
   values of ops and axioms, as we rely on Coq's other definition
   mechanisms to do that.
*)
type spec = {
  spec_ops : op_ctx;
  spec_axioms : Id.t list
}


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, indexed by spec global
refs *)
let spec_table = ref (Mindmap.empty)

(* Register a spec in the spec_table *)
let register_global_spec spec_lident spec =
  let spec_globref = lookup_spec_globref (Ident spec_lident) in
  (*
  Format.eprintf "\nregister_global_spec: ind (name = %s, id = %i)\n"
                 (MutInd.to_string ind) i
   *)
  spec_table := Mindmap.add spec_globref spec !spec_table

(* Look up a spec and its spec_globref from a local reference to the
   spec's module, which is the user-visible way to name specs *)
let lookup_spec_and_globref ref =
  let globref = lookup_spec_globref ref in
  (Mindmap.find globref !spec_table, globref)

(* Look up a spec from a local reference to its module, which is the
   user-visible way to name specs *)
let lookup_spec ref = fst (lookup_spec_and_globref ref)


(***
 *** Interpreting specs into type-classes
 ***)

(* Interpret a spec term (which for now is just a name) into a spec
   and a local reference to that spec *)
let rec interp_spec_term sterm : spec * spec_locref =
  match sterm with
  | SpecRef ref ->
     (lookup_spec ref, spec_locref_of_ref ref)
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
     raise (spec_term_loc sterm) (Failure "Imports not handled yet")


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
