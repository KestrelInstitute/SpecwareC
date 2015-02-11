
DECLARE PLUGIN "specware"

open Names
open Loc
open Libnames
open Pp
open Vernacexpr
open Vernacentries
open Constrexpr
open Misctypes

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

(* Add a definition to the current Coq image *)
let add_definition id params type_opt body =
  interp
    (located_loc id,
     VernacDefinition
       ((None, Decl_kinds.Definition), id,
        DefineBody (params, None, body, type_opt)))

(* Add a type-class to the current Coq image, where is_op_class says
   whether to add an operational type-class in Type (if true) or a
   normal type-class in Prop (if false) *)
let add_typeclass class_id is_op_class params fields =
  interp
    (located_loc class_id,
     VernacInductive (false, Decl_kinds.BiFinite,
                      [((false, class_id), params,
                        Some (if is_op_class then type_expr else prop_expr),
                        Class is_op_class,
                        if is_op_class then
                          let (id, tp, _) = List.hd fields in
                          Constructors [false, (id, Constrexpr_ops.mkCProdN (located_loc id) params tp)]
                        else
                          RecordDecl (None, List.map mk_record_field fields)),
                       []]))

(* Perform some operation(s) inside a newly-defined module *)
let within_module mod_name f =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []));
  f ();
  interp (loc, VernacEndSegment mod_name)


(***
 *** The data-types for specifying specs (ha ha)
 ***)

(* The syntactic representation (parsed but not yet type-checked) of a
   single spec entry, i.e., a single element of a spec. This is either
   a normal Gallina top-level command (though only certain ones are
   allowed), or is a spec import form *)
(* FIXME HERE: use this new approach!
type spec_entry =
  | GallinaEntry of vernac_expr
  (* Import of another spec: contains the spec name and a list of
    "with clauses" that define some declared ops of that spec *)
  | ImportEntry of lident * (Id.t * Constrexpr.constr_expr) list
 *)

(* The syntactic representation (parsed but not yet type-checked) of a
   single spec entry, i.e., a single element of a spec *)
type spec_entry =
  (* Declaration of an op: contains its name and type *)
  | OpEntry of lident * Constrexpr.constr_expr
  (* Definition of an op: contains its name, type, and value *)
  | OpDefEntry of lident * Constrexpr.constr_expr option * Constrexpr.constr_expr
  (* Declaration of an axiom: contains its name and type *)
  | AxEntry of lident * Constrexpr.constr_expr
  (* Import of another spec: contains the spec name and a list of
    "with clauses" that define some declared ops of that spec *)
  | ImportEntry of lident * (Id.t * Constrexpr.constr_expr) list

(* An op context specifies the ops that are currently in scope, and,
   for each op, whether it is defined or just declared.

   NOTE: op contexts always have the most recently declared or defined
   op first, i.e., the first op in a spec is the last op in an op
   context; this is to make it easy to append ops as we go *)
type op_ctx_elem = | OpCtx_Decl of Id.t | OpCtx_Defn of Id.t
type op_ctx = op_ctx_elem list

(* Get the identifier from an op_ctx_elem *)
let op_ctx_elem_id op_ctx_elem =
  match op_ctx_elem with
  | OpCtx_Decl id -> id
  | OpCtx_Defn id -> id

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
                 Default Decl_kinds.Implicit,
                 mk_var (Loc.dummy_loc, add_suffix id "class"))

(* Convert an op_ctx to a list of class parameters, one for each
   OpCtx_Decl in the context (remember: op_ctx is reversed) *)
let op_ctx_to_params op_ctx =
  List.rev_map op_ctx_elem_to_param op_ctx

(*
(* The axiom context specifies fields in the propositional class *)
type ax_ctx_elem =
  (* Axioms are specified by their name and type *)
  | AxSpec of Id.t * Constrexpr.constr_expr
  (* Imports are specified by the spec being imported and the list of
     "with" clauses giving additional definitions to that spec *)
  | ImportSpec of Id.t * ((Id.t * Constrexpr.constr_expr) list)

type ax_ctx = ax_ctx_elem list
 *)


(***
 *** Interpreting specs into type-classes
 ***)

(* Interpret a list of spec_entries into a series of typeclasses and
   definitions, given an op_ctx and the current list of fields, in
   reverse order, to go into the axiom typeclass *)
let rec interp_spec_entries spec_name op_ctx ax_fields entries =
  match entries with
  | [] ->
     (* At the end of all entries, make the final, propositional
        type-class for all the axioms and imports *)
     add_typeclass spec_name false
                   (op_ctx_to_params op_ctx) (List.rev ax_fields)
  | OpEntry (op_name, op_type) :: entries' ->
     (* For an op declaration, make an operational typeclass
        Class op__class {op_params} := { op : op_type }
      *)
     add_typeclass (add_suffix_l op_name "class") true
                   (op_ctx_to_params op_ctx)
                   [(op_name, op_type, false)] ;
     interp_spec_entries spec_name (op_ctx_cons_decl op_name op_ctx)
                         ax_fields entries'
  | OpDefEntry (op_name, op_type_opt, op_body) :: entries' ->
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
     let params = op_ctx_to_params op_ctx in
     let op_def_id = add_suffix_l op_name "def" in
     add_definition op_name (op_ctx_to_params op_ctx) op_type_opt op_body ;
     add_typeclass (add_suffix_l op_name "class") true params
                   [(op_def_id, op_type, false)] ;
     interp_spec_entries spec_name (op_ctx_cons_defn op_name op_ctx)
                         (((add_suffix_l op_name "eq"),
                           (mk_ident_equality op_def_id op_name),
                           false)
                          :: ax_fields)
                         entries'
  | AxEntry (ax_name, ax_type) :: entries' ->
     (* For axioms, just make a record field for the final,
        propositional type-class and pass it forward *)
     interp_spec_entries spec_name op_ctx
                         ((ax_name, ax_type, false) :: ax_fields)
                         entries'
  | ImportEntry (import_spec, with_defs) :: entries' ->
     raise (located_loc import_spec) (Failure "Imports not handled yet")


(* Top-level entrypoint to interpret a spec expression *)
(* FIXME: put each spec inside a module *)
let interp_spec spec_name entries =
  within_module spec_name
                (fun () -> interp_spec_entries spec_name [] [] entries)
;;


(***
 *** Additions to the Coq parser
 ***)

(* FIXME: get the locations of all the identifiers right! *)

(* New syntactic class to parse individual spec entries *)
VERNAC ARGUMENT EXTEND spec_entry
  | [ "Variable" ident(nm) ":" constr(tp) ] -> [ OpEntry ((loc, nm), tp) ]
  | [ "Definition" ident(nm) ":" constr(tp) ":=" constr(body) ] -> [ OpDefEntry ((loc, nm), Some tp, body) ]
  | [ "Definition" ident(nm) ":=" constr(body) ] -> [ OpDefEntry ((loc, nm), None, body) ]
  | [ "Axiom" ident(nm) ":" constr(tp) ] -> [ AxEntry ((loc, nm), tp) ]
END

type spec_entries = spec_entry list

(* New syntactic class to parse lists of one or more spec entries,
   separated by semicolons *)
VERNAC ARGUMENT EXTEND spec_entries
  | [ spec_entry(entry) ";" spec_entries(rest) ] -> [ entry::rest ]
  | [ spec_entry(entry) ] -> [ [entry] ]
END

(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec
  | [ "Spec" ident(spec_name) "{" spec_entries(entries) "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ interp_spec (dummy_loc, spec_name) entries ]
  | [ "Spec" ident(spec_name) "{" "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ interp_spec (dummy_loc, spec_name) [] ]
END
