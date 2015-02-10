
DECLARE PLUGIN "specware"

open Names
open Pp

let pp_constr fmt c = Pp.pp_with fmt (Printer.pr_constr c)

(* Helper terms *)
let empty_loc = FIXME
let type_expr = CSort (empty_loc, GType [])
let prop_expr = CSort (empty_loc, GProp)

(* The syntactic representation of a single spec entry *)
type spec_entry =
  (* Declaration of an op: contains its name and type *)
  | Op_decl of Id.t located * Constrexpr.constr_expr
  (* Definition of an op: contains its name, type, and value *)
  | Op_def of Id.t located * Constrexpr.constr_expr option * Constrexpr.constr_expr
  (* Declaration of an axiom: contains its name and type *)
  | Ax_decl of Id.t located * Constrexpr.constr_expr

(* An op context specifies the ops that are currently in scope, and,
   for each op, whether it is defined or just declared *)
type op_ctx_elem = | OpDecl Id.t | OpDefn Id.t
type op_ctx = op_ctx_elem list

(* Convert an op_ctx to a list of class parameters *)
let op_ctx_to_binders op_ctx =
  [] (* FIXME *)

(* A field specifier denotes a field in the final, proposition
   type-class built for a spec. *)
type field_spec =
  | AxField of Id.t * Constrexpr.constr_expr
  | ImportField of Id.t * ((Id.t * Constrexpr.constr_expr) list)

(* Add a type-class for a declared op *)
let add_declared_op_class op_name op_ctx op_type =
  let class_name = op_name in (* FIXME: add suffix "__class" *)
  vernac_inductive false false BiFinite
                   (((false, class_name),
                     op_ctx_to_binders op_ctx,
                     Some type_expr,
                     Class true,
                     RecordDecl (None,
                                 [(((None,
                                    AssumExpr (op_name, op_type)),
                                    None), [])])),
                    [])

let process_spec_entries entries =
  List.iter
    (fun entry -> match entry with
                  | Op_decl (nm,tp) -> Format.eprintf "\nFound op decl %s\n" (Id.to_string nm)
                  | Op_def (nm,tp,body) -> Format.eprintf "\nFound op def %s\n" (Id.to_string nm)
                  | Ax_decl (nm,tp) -> Format.eprintf "\nFound axiom %s\n" (Id.to_string nm)
    )
    entries

(* New syntactic class to parse individual spec entries *)
VERNAC ARGUMENT EXTEND spec_entry
  | [ "Variable" identref(nm) ":" constr(tp) ] -> [ Op_decl (nm, tp) ]
  | [ "Definition" identref(nm) ":" constr(tp) ":=" constr(body) ] -> [ Op_def (nm, Some tp, body) ]
  | [ "Definition" identref(nm) ":=" constr(body) ] -> [ Op_def (nm, None, body) ]
  | [ "Axiom" identref(nm) ":" constr(tp) ] -> [ Ax_decl (nm, tp) ]
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
  | [ "Spec" identref(spec_name) "{" spec_entries(entries) "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ process_spec_entries entries ]
  | [ "Spec" identref(spec_name) "{" "}" ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ process_spec_entries [] ]
END
