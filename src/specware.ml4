
DECLARE PLUGIN "specware"

open Names
open Pp
open Vernacexpr
open Vernacentries
open Constrexpr

(***
 *** Helper functions for interacting with Coq
 ***)

(* Syntactic expressions for the sorts Type and Prop *)
let type_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GType [])
let prop_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GProp)

(* Pretty-print a term (a "construction") *)
let pp_constr fmt c = Pp.pp_with fmt (Printer.pr_constr c)

(* Append a suffix to an Id, with "__" in between *)
let add_suffix id suffix =
  Id.of_string (Id.to_string id ^ "__" ^ suffix)

(* Make (the syntactic representation of) a single record field,
   filling in default (None) values for all the extra information such
   as notations, priority, etc. *)
let mk_record_field name tp =
  (((None, AssumExpr (name, tp)), None), [])

(* Add a type-class to the current Coq image, where is_op_class says
   whether to add an operational type-class in Type (if true) or a
   normal type-class in Prop (if false) *)
let add_typeclass class_name is_op_class params fields =
  raise (Failure "add_typeclass")
(*
  vernac_inductive false false BiFinite
                   (((false, class_name), params,
                     Some (if is_op_class then type_expr else prop_expr),
                     Class is_op_class,
                     RecordDecl (None, fields)),
                    [])
 *)


(***
 *** Processing specs into type-classes
 ***)

(* The syntactic representation (parsed but not yet type-checked) of a
   single spec entry *)
type spec_entry =
  (* Declaration of an op: contains its name and type *)
  | Op_decl of lident * Constrexpr.constr_expr
  (* Definition of an op: contains its name, type, and value *)
  | Op_def of lident * Constrexpr.constr_expr option * Constrexpr.constr_expr
  (* Declaration of an axiom: contains its name and type *)
  | Ax_decl of lident * Constrexpr.constr_expr

(* FIXME: add imports to the above *)

(* An op context specifies the ops that are currently in scope, and,
   for each op, whether it is defined or just declared *)
type op_ctx_elem = | OpDecl of Id.t | OpDefn of Id.t
type op_ctx = op_ctx_elem list

(* Convert an op_ctx to a list of class parameters, one for each
   OpDecl in the context *)
let rec op_ctx_to_binders op_ctx =
  match op_ctx with
  | [] -> []
  | (OpDefn _) :: op_ctx' -> op_ctx_to_binders op_ctx'
  | (OpDecl nm) :: op_ctx' ->
     (LocalRawAssum ([(Loc.dummy_loc, Name (add_suffix nm "param"))],
                     Default Decl_kinds.Implicit,
                     CEvar (Loc.dummy_loc, add_suffix nm "class", [])))
     :: op_ctx_to_binders op_ctx'

(* A field specifier denotes a field in the final, proposition
   type-class built for a spec *)
type field_spec =
  | AxField of Id.t * Constrexpr.constr_expr
  | ImportField of Id.t * ((Id.t * Constrexpr.constr_expr) list)

(* Add a type-class for a declared op *)
let add_declared_op_class op_name op_ctx op_type =
  let class_name = op_name in (* FIXME: add suffix "__class" *)
  add_typeclass class_name true
                (op_ctx_to_binders op_ctx)
                [mk_record_field op_name op_type]

let process_spec_entries entries =
  List.iter
    (fun entry -> match entry with
                  | Op_decl (nm,tp) -> Format.eprintf "\nFound op decl %s\n" (Id.to_string (snd nm))
                  | Op_def (nm,tp,body) -> Format.eprintf "\nFound op def %s\n" (Id.to_string (snd nm))
                  | Ax_decl (nm,tp) -> Format.eprintf "\nFound axiom %s\n" (Id.to_string (snd nm))
    )
    entries


(***
 *** Additions to the Coq parser
 ***)

(* New syntactic class to parse individual spec entries *)
VERNAC ARGUMENT EXTEND spec_entry
  | [ "Variable" ident(nm) ":" constr(tp) ] -> [ Op_decl ((loc, nm), tp) ]
  | [ "Definition" ident(nm) ":" constr(tp) ":=" constr(body) ] -> [ Op_def ((loc, nm), Some tp, body) ]
  | [ "Definition" ident(nm) ":=" constr(body) ] -> [ Op_def ((loc, nm), None, body) ]
  | [ "Axiom" ident(nm) ":" constr(tp) ] -> [ Ax_decl ((loc, nm), tp) ]
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
    -> [ process_spec_entries entries ]
  | [ "Spec" ident(spec_name) "{" "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ process_spec_entries [] ]
END
