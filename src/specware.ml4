
DECLARE PLUGIN "specware"

open Util_specware

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

(* FIXME: documentation *)
type spec_import = {
  spec_import_ops : Id.t list;
  spec_import_ax_map : (Id.t * Id.t) list;
  spec_import_class_qualid : qualid;
  spec_import_number : int
}

(* A spec contains its name, its module path, and its op and axiom names. Note
that ops and axioms --- collectively called the "fields" of the spec --- are
stored in reverse order, for efficiency of adding new ones. *)
type spec = {
  spec_name : Id.t;
  spec_path : DirPath.t;
  spec_ops : (Id.t * constr_expr * constr_expr option) list;
  spec_axioms : (Id.t * constr_expr) list;
  spec_imports : spec_import list
}

(* Create an empty spec with the given name *)
let make_empty_spec spec_id =
  { spec_name = spec_id; spec_path = Lib.cwd_except_section ();
    spec_ops = []; spec_axioms = []; spec_imports = [] }

(* Whether spec contains an op or axiom named f *)
let contains_field spec f =
  List.exists (fun (f',_,_) -> Id.equal f f') spec.spec_ops ||
    List.exists (fun (f', _) -> Id.equal f f') spec.spec_axioms

(* Whether field f has an associated oppred *)
let field_has_oppred spec f =
  try
    (match List.find (fun (f',_,_) -> Id.equal f f') spec.spec_ops with
     | (_,_,Some _) -> true
     | (_,_,None) -> false)
  with Not_found -> raise dummy_loc (Failure "field_has_oppred")

(* Check that a field (op or axiom) of the given name exists in the current spec *)
let spec_field_exists f =
  let res = Nametab.exists_cci (Lib.make_path f) in
  let _ = debug_printf 2 "@[spec_field_exists (%s): %B@]\n" (Id.to_string f) res in
  res

(* Map spec import number i to an Id *)
let spec_import_id i =
  Id.of_string ("spec_instance__" ^ string_of_int i)

(* Find an unused import number in spec *)
let find_unused_import_id spec =
  let slots = Array.make (List.length spec.spec_imports) false in
  let _ = List.iter (fun imp -> slots.(imp.spec_import_number) <- true)
                    spec.spec_imports in
  let i = ref 0 in
  let _ = while !i < Array.length slots && slots.(!i) do
            i := !i + 1
          done
  in
  !i

(* Remove fields that no longer exist (because of potential Undos) *)
let filter_nonexistent_fields_and_imports spec =
  { spec with
    spec_ops = List.filter (fun (id, _,_) ->
                            spec_field_exists id) spec.spec_ops;
    spec_axioms = List.filter (fun (id,_) -> spec_field_exists id) spec.spec_axioms;
    spec_imports =
      List.filter (fun imp ->
                   spec_field_exists (spec_import_id imp.spec_import_number))
                  spec.spec_imports }


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

(* A description of strings that parses into Id.t *)
let id_descr : (Id.t, Id.t) constr_descr =
  Descr_Iso ("id", Id.of_string, Id.to_string, string_fast_descr)

(* A description of axiom pairs: optimizes pair_descr by using the ax_pair
operator from Spec.v *)
let ax_pair_descr : (Id.t * Constr.t, Id.t * constr_expr) constr_descr =
  Descr_Direct
    ((fun constr ->
      destruct_constr (pair_descr id_descr Descr_Constr)
                      (hnf_constr constr)),
     (fun (f, tp) ->
      mkAppC (mk_reference ["Specware"; "Spec"] "ax_pair",
              [mk_string (Id.to_string f); tp])))

(* The description of a list of axioms *)
let axiom_list_descr : ((Id.t * Constr.t) list,
                        (Id.t * constr_expr) list) constr_descr =
  list_descr ax_pair_descr

type spec_fields =
    (Id.t * constr_expr * constr_expr option) list * (Id.t * constr_expr) list
type spec_fields_constr =
    (Id.t * Constr.t * Constr.t option) list * (Id.t * Constr.t) list

(* The description of the Spec inductive type *)
let spec_descr : (spec_fields_constr,spec_fields) constr_descr =
  Descr_Rec
    (fun spec_descr ->
     Descr_Iso
       ("Spec",
        (function
          | Left (f, (tp, (oppred, ((ops, axioms), ())))) ->
             ((f, tp, oppred)::ops, axioms)
          | Right (Left (axioms, ())) -> ([], axioms)
          | Right (Right emp) -> emp.elim_empty),
        (function
          | ((f,tp,oppred)::ops', axioms) ->
             Left (f, (tp, (oppred, ((ops', axioms), ()))))
          | ([], axioms) -> Right (Left (axioms, ()))),
        quaternary_ctor
          ["Specware"; "Spec"] "Spec_ConsOp"
          id_descr (fun _ -> Descr_Constr) (fun _ _ -> option_descr Descr_Constr)
          (fun f_sum _ _ ->
           let f = match f_sum with Left f -> f | Right f -> f in
           Descr_ConstrMap
             ((fun rest_c ->
               hnf_constr
                 (Term.mkApp
                    (rest_c,
                     [| Term.mkVar f; Term.mkVar (field_proof_id f) |]))),
              (fun rest_expr ->
               (mkCLambdaN
                  dummy_loc
                  [LocalRawAssum ([dummy_loc, Name f], Default Explicit,
                                  mk_var (dummy_loc, field_class_id f));
                   LocalRawAssum ([dummy_loc, Name (field_proof_id f)], Default Explicit,
                                  CHole (dummy_loc, None, IntroAnonymous, None))]
                  rest_expr)),
              spec_descr))
          (unary_ctor
             ["Specware"; "Spec"] "Spec_Axioms" axiom_list_descr
             Descr_Fail)))

(* Build a term of type Spec that represents a spec *)
let build_spec_repr loc spec : constr_expr =
  build_constr_expr spec_descr (List.rev spec.spec_ops, spec.spec_axioms)

exception MalformedSpec of Constr.t * string * Constr.t

(* Destruct a constr of type Spec into a list of ops and axioms; NOTE: this
returns the ops in non-reversed order, unlike in the type spec *)
let destruct_spec_repr constr =
  try
    destruct_constr spec_descr (hnf_constr constr)
  with DescrFailed (tag,sub_constr) ->
    raise dummy_loc (MalformedSpec (constr,tag,sub_constr))

type refinement_import =
    constr_expr * constr_expr * constr_expr
type refinement_import_constr = {
  ref_import_fromspec: Constr.t;
  ref_import_interp: Constr.t;
  ref_import_class: global_reference;
  ref_import_iso: Constr.t
}

(* A description of the RefinementImport type *)
let refinement_import_descr :
      (refinement_import_constr, refinement_import) constr_descr =
  Descr_Iso
    ("RefinementImport",
     (function
       | Left (x1, (x2, (x3, (x4, ())))) ->
          let gr =
            (match Term.kind_of_term x3 with
             | Term.Const (c, _) -> ConstRef c
             | Term.Ind (ind, _) -> IndRef ind
             | Term.Construct (c, _) -> ConstructRef c
             | _ -> raise dummy_loc DescrFailedInternal)
          in
          {ref_import_fromspec = x1;
           ref_import_interp = x2;
           ref_import_class = gr;
           ref_import_iso = x4}
       | Right emp -> emp.elim_empty),
     (fun (x1,x2,x3) ->
      Left ((), (x1, (x2, (x3, ()))))),
     quaternary_ctor
       ["Specware"; "Spec"] "Build_RefinementImport"
       (hole_descr Descr_Constr) (fun _ -> Descr_Constr)
       (fun _ _ -> Descr_Constr) (fun _ _ _ -> Descr_Constr)
       Descr_Fail)

type refinementof = spec_fields * constr_expr * refinement_import list
type refinementof_constr =
    spec_fields_constr * Constr.t * refinement_import_constr list

(* A description of the RefinementOf type *)
let refinementof_descr : (refinementof_constr, refinementof) constr_descr =
  Descr_Iso
    ("RefinementOf",
     (function
       | Left (x1, (x2, (x3, ()))) -> (x1, x2, x3)
       | Right emp -> emp.elim_empty),
     (fun (x1, x2, x3) ->
      Left (x1, (x2, (x3, ())))),
     ternary_ctor
       ["Specware"; "Spec"] "Build_RefinementOf"
       spec_descr (fun _ -> Descr_Constr)
       (fun _ _ -> list_descr refinement_import_descr)
       Descr_Fail)

exception MalformedRefinement of Constr.t * string * Constr.t

let destruct_refinementof constr =
  try
    destruct_constr refinementof_descr (hnf_constr constr)
  with DescrFailed (tag,sub_constr) ->
    raise dummy_loc (MalformedRefinement (constr,tag,sub_constr))


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
       current_spec := Some (filter_nonexistent_fields_and_imports spec)
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
  (* Build the spec representation spec__repr *)
  let _ = add_definition (loc, spec_repr_id spec.spec_name) [] None
                         (build_spec_repr loc spec) in
  (* Build a proof spec__iso that spec__repr is isomorphic to the spec *)
  let _ = add_term_instance
            (loc, Name spec_iso_id spec.spec_name) []
            (mkAppC (mk_reference ["Specware"; "Spec"] "IsoToSpec",
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
  (* Add an instance for each import in the spec *)
  let inst_counter = ref 1 in
  let mk_inst_name () =
    let res = add_suffix spec.spec_name ("inst" ^ string_of_int !inst_counter) in
    let _ = inst_counter := !inst_counter + 1 in
    res
  in
  let _ =
    List.iter
      (fun imp ->
       add_term_instance
         (dummy_loc, Name (mk_inst_name ()))
         [LocalRawAssum ([dummy_loc, Anonymous],
                         Generalized (Implicit, Implicit, false),
                         mk_var (dummy_loc, spec.spec_name))]
         (mkRefC (Qualid (dummy_loc,imp.spec_import_class_qualid)))
         (mkAppC (mk_var (dummy_loc,
                          spec_import_id imp.spec_import_number),
                  concat_map
                    (fun f -> if field_has_oppred spec f then
                                [mk_var (dummy_loc, f);
                                 mk_var (dummy_loc, field_proof_id f)]
                              else [mk_var (dummy_loc, f)])
                    imp.spec_import_ops
                  @
                    [CRecord (loc, None,
                              List.map (fun (f_from,f_to) ->
                                        (Ident (dummy_loc,f_from),
                                         mk_var (dummy_loc,f_to)))
                                       imp.spec_import_ax_map)])))
      spec.spec_imports
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
 *** Spec Imports
 ***)

(* Import all the ops and axioms given in a RefinementOf object *)
let import_refinement_constr loc constr =
  let (evd,env) = Lemmas.get_current_context () in
  let ((ops,axioms),interp,imports) = destruct_refinementof constr in
  let _ =
    List.iter (fun (f,tp,oppred) ->
               add_spec_field
                 false
                 (loc, f)
                 (Constrextern.extern_constr true env evd tp)
                 (map_opt (Constrextern.extern_constr true env evd) oppred)) ops
  in
  let _ =
    List.iter
      (fun (ax_name,ax_tp) ->
       add_spec_field true
                      (loc, ax_name)
                      (Constrextern.extern_constr true env evd ax_tp)
                      None)
      axioms
  in
  update_current_spec
    loc
    (fun spec ->
     let new_imports =
       List.map
         (fun refimp ->
          let imp_num = find_unused_import_id spec in
          let interp_expr =
            Constrextern.extern_constr true env evd refimp.ref_import_interp
          in
          let _ =
            add_definition (loc,spec_import_id imp_num) [] None interp_expr
          in
          {spec_import_ops = List.map (fun (f,_,_) -> f) ops;
           spec_import_ax_map = List.map (fun (f,_) -> (f,f)) axioms;
           spec_import_class_qualid = qualid_of_global refimp.ref_import_class;
           spec_import_number = imp_num}) imports in
     {spec with spec_imports = spec.spec_imports @ new_imports})

(* Same as above, but take in a term for a Spec representation object *)
let import_refinement_constr_expr loc constr_expr =
  let (evd,env) = Lemmas.get_current_context () in
  let (constr,_) = Constrintern.interp_constr env evd constr_expr in
  import_refinement_constr loc constr


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

  | [ "Spec" "ImportTerm" constr(tm) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_refinement_constr_expr dummy_loc tm) ]

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
