
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
let spec_repr_id s_id = add_suffix s_id "Spec"

(* The name of the parameteric ops constructor for a spec named s_id *)
let spec_ops_id s_id = add_suffix s_id "ops"

(* The name of the IsoToSpec proof for a spec named s_id *)
let spec_iso_id s_id = add_suffix s_id "Iso"

(* Get the Id for the interppretation for import number i *)
let spec_import_id i =
  add_suffix (Id.of_string "spec") ("import" ^ string_of_int i)

(* Get the Id for the interppretation for import number i *)
let spec_import_ops_id i =
  add_suffix (Id.of_string "spec_ops") ("import" ^ string_of_int i)

(* Get the Id for the interppretation for import number i *)
let spec_import_model_id i =
  add_suffix (Id.of_string "spec_model") ("import" ^ string_of_int i)

(* Get the Id for the jth instance generated from the ith import *)
let spec_import_instance_id i j =
  add_suffix
    (add_suffix (Id.of_string "spec") ("import" ^ string_of_int i))
    ("instance" ^ string_of_int j)

(* The variable name for the implicit spec argument of a morphism instance *)
let morph_spec_arg_id = Id.of_string "Spec"


(***
 *** Specware-Specific Symbols
 ***)

(* The logical path to the Specware.Spec module *)
let specware_mod = ["Specware"; "Spec"]

(* Build a reference to a Specware-specific symbol *)
let mk_specware_ref str =
  mk_reference specware_mod str


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

(* Return a local reference to the Spec object for a spec *)
let spec_repr_qualid locref =
  qualid_cons locref (spec_repr_id (spec_locref_basename locref))

let spec_repr_ref loc locref =
  Qualid (loc, spec_repr_qualid locref)

(* A global reference to a spec is a global reference to the spec's
   module *)
type spec_globref = module_path

(* Get the spec_globref from a global reference to a spec's typeclass *)
let spec_globref_of_classref gr =
  global_modpath gr

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
let spec_globref_to_locref spec_globref =
  Nametab.shortest_qualid_of_module spec_globref

(* Build a reference to a field in a global spec *)
(* FIXME: this should not go through a locref *)
let field_in_global_spec globref fname =
  field_in_spec (spec_globref_to_locref globref) fname

(* Build a reference to the axiom typeclass of a global spec *)
let global_spec_typeclass_ref loc globref =
  spec_typeclass_ref loc (spec_globref_to_locref globref)

let global_field_in_global_spec globref fname =
  try Nametab.locate (field_in_global_spec globref fname)
  with Not_found ->
    raise dummy_loc (Failure "global_field_in_global_spec")

(* Return a reference to the Spec object for a spec *)
let global_spec_repr_ref loc globref =
  spec_repr_ref loc (spec_globref_to_locref globref)

(* Return the constant for the Spec object of a spec *)
let global_spec_repr_constant loc globref =
  try
    (match Nametab.locate (spec_repr_qualid (spec_globref_to_locref globref)) with
     | ConstRef c -> c
     | _ -> raise loc (Failure "global_spec_repr_constant"))
  with Not_found ->
    raise dummy_loc (Failure "global_spec_repr_constant")


(***
 *** Operations on Specs
 ***)

(* FIXME: documentation *)
(*
type spec_import = {
  spec_import_ops : Id.t list;
  spec_import_ax_map : (Id.t * Id.t) list;
  spec_import_class_qualid : qualid
}
 *)

(* A spec contains its name, its module path, and its op and axiom names. Note
that ops and axioms --- collectively called the "fields" of the spec --- are
stored in reverse order, for efficiency of adding new ones. *)
type spec = {
  spec_name : Id.t;
  spec_path : DirPath.t;
  spec_ops : (Id.t * constr_expr * constr_expr option) list;
  spec_axioms : (Id.t * constr_expr) list;
  spec_imports : (int * (spec_globref * Hints.hints_entry list) list) list
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

(* Find an unused import number in spec *)
let find_unused_import_id spec =
  let slots = Array.make (List.length spec.spec_imports) false in
  let _ = List.iter (fun imp -> slots.(fst imp) <- true)
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
      List.filter (fun (imp_num,_) ->
                   spec_field_exists (spec_import_id imp_num))
                  spec.spec_imports }

(* Build a map from each free variable implied by a list of ops (including
f__param and f__proof for each field f) to the result of (builder is_pf var),
where is_pf is true iff var is an f__proof variable (instead of f__param) *)
let build_map_for_ops builder ops =
  List.fold_left
    (fun map (op_id, op_tp, oppred) ->
     let map1 = Id.Map.add
                  (field_param_id op_id)
                  (builder false (field_param_id op_id))
                  map
     in
     match oppred with
     | None -> map1
     | Some pred ->
        Id.Map.add (field_proof_id op_id)
                   (builder true (field_proof_id op_id))
                   map1
    )
    Id.Map.empty ops


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
  try MPmap.find globref !spec_table
  with Not_found ->
    raise dummy_loc (Failure "lookup_global_spec")

(* Look up a spec and its spec_globref from a local spec reference *)
let lookup_spec_and_globref locref =
  let globref = lookup_spec_globref locref in
  (lookup_global_spec globref, globref)

(* Look up a spec from a local spec reference *)
let lookup_spec locref = fst (lookup_spec_and_globref locref)


(***
 *** Inductive Descriptions of Specs and Refinements
 ***)

(* A description of strings that parses into Id.t *)
let id_descr : (Id.t, Id.t) constr_descr =
  hnf_descr (Descr_Iso ("id", Id.of_string, Id.to_string, string_fast_descr))

(* A description of axiom pairs: optimizes pair_descr by using the ax_pair
operator from Spec.v *)
let ax_pair_descr : (Id.t * Constr.t, Id.t * constr_expr) constr_descr =
  Descr_Direct
    ((fun constr ->
      destruct_constr (pair_descr id_descr Descr_Constr)
                      (hnf_constr constr)),
     (fun (f, tp) ->
      mkAppC (mk_specware_ref "ax_pair",
              [mk_string (Id.to_string f); tp])))

(* The description of a list of axioms *)
let axiom_list_descr : ((Id.t * Constr.t) list,
                        (Id.t * constr_expr) list) constr_descr =
  list_descr ax_pair_descr

type spec_fields =
    (Id.t * constr_expr * constr_expr option) list * (Id.t * constr_expr) list
type spec_fields_constr =
    (Id.t * Constr.t * Constr.t option) list * (Id.t * Constr.t) list

(* The description of the Spec inductive type.

NOTE: there is some trickiness here, where we capture the fields themselves, and
not the f__param arguments, as bound variables when we build a Spec object, and,
similarly, we apply the "rest" argument of a Spec object to variable f, not
f__param, when we destruct a Spec object. This will mess us up if any
types/definitions ever do use an f__param variable directly. *)
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
          (hnf_descr id_descr) (fun _ -> Descr_Constr) (fun _ _ -> option_descr Descr_Constr)
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
             ["Specware"; "Spec"] "Spec_Axioms" (hnf_descr axiom_list_descr)
             Descr_Fail)))

(* Build a term of type Spec that represents a spec *)
let build_spec_repr loc spec : constr_expr =
  build_constr_expr spec_descr (List.rev spec.spec_ops, List.rev spec.spec_axioms)

exception MalformedSpec of Constr.t * string * Constr.t

(* Destruct a constr of type Spec into a list of ops and axioms; NOTE: this
returns the ops in non-reversed order, unlike in the type spec *)
let destruct_spec_repr constr =
  try
    destruct_constr spec_descr (hnf_constr constr)
  with DescrFailed (tag,sub_constr) ->
    raise dummy_loc (MalformedSpec (constr,tag,sub_constr))

type refinement_import = constr_expr * constr_expr
type refinement_import_constr = {
  ref_import_fromspec: spec_globref;
  ref_import_interp: Constr.t
}


exception NonGlobalSpec of Constr.t

(* Reduce constr until it is a global_reference to a variable XXX.XXX__Spec,
where XXX is some spec module registerd in spec_table. *)
(* README: As another way to do this, we could repeatedly reduce with CBN, only
allowing constants to be expanded if we see them in the term and they do not end
in __Spec *)
let destruct_spec_globref_constr constr =
  let constr_red =
    reduce_constr
      [Cbn (Redops.make_red_flag
              [FBeta;FIota;FZeta;
               FDeltaBut (List.map
                            (fun (spec_globref,_) ->
                             AN (global_spec_repr_ref dummy_loc spec_globref))
                            (MPmap.bindings !spec_table))])]
      constr
  in
  match Term.kind_of_term constr_red with
  | Term.Const (c, _) -> Constant.modpath c
  | Term.Ind (ind, _) -> ind_modpath ind
  | Term.Construct (c, _) -> constr_modpath c
  | _ -> raise dummy_loc (NonGlobalSpec constr)

(* A description of the RefinementImport type *)
let refinement_import_descr :
      (refinement_import_constr, refinement_import) constr_descr =
  Descr_Iso
    ("RefinementImport",
     (function
       | Left (_, (x1, (x2, ()))) ->
          {ref_import_fromspec = destruct_spec_globref_constr x1;
           ref_import_interp = x2}
       | Right emp -> emp.elim_empty),
     (fun (x1,x2) ->
      Left ((), (x1, (x2, ())))),
     ternary_ctor
       ["Specware"; "Spec"] "Build_RefinementImport"
       (hole_descr Descr_Constr) (fun _ -> Descr_Constr)
       (fun _ _ -> Descr_Constr)
       Descr_Fail)

type refinementof = spec_fields * constr_expr * refinement_import list
type refinementof_constr =
    spec_fields_constr * Constr.t * refinement_import_constr list

(* A description of the RefinementOf type *)
let refinementof_descr : (refinementof_constr, refinementof) constr_descr =
  Descr_Iso
    ("RefinementOf",
     (function
       | Left (_, (x1, (x2, (x3, ())))) -> (x1, x2, x3)
       | Right emp -> emp.elim_empty),
     (fun (x1, x2, x3) ->
      Left ((), (x1, (x2, (x3, ()))))),
     quaternary_ctor
       ["Specware"; "Spec"] "Build_RefinementOf"
       (hole_descr Descr_Constr)
       (fun _ -> hnf_descr spec_descr)
       (fun _ _ -> Descr_Constr)
       (fun _ _ _ -> hnf_descr (list_descr (hnf_descr refinement_import_descr)))
       Descr_Fail)

exception MalformedRefinement of Constr.t * string * Constr.t

let destruct_refinementof constr =
  try
    destruct_constr refinementof_descr (hnf_constr constr)
  with DescrFailed (tag,sub_constr) ->
    raise dummy_loc (MalformedRefinement (constr,tag,sub_constr))


(***
 *** Inductive Descriptions of Ops and Models
 ***)

(* A description of the spec_ops S type for any given spec S.

NOTE: does not use any reduction, since it is used (in the import code, below)
in an extended environment with free variables. Thus, if you call
destruct_constr with spec_ops_descr, you need to be sure the Constr.t you are
applying it to is already normalized as needed. *)
let spec_ops_descr : ((Constr.t * Constr.t) list,
                      (constr_expr * constr_expr) list) constr_descr =
  Descr_Rec
    (fun spec_ops_descr ->
     Descr_Iso
       ("spec_ops",
        (function
          | Left (_, (_, (x1, (Left (_, (_, (x2, (x3, ())))), ())))) -> (x1,x2)::x3
          | Left (_, (_, (x1, (Right emp, ())))) -> emp.elim_empty
          | Right (Left ()) -> []
          | Right (Right emp) -> emp.elim_empty),
        (function
          | [] -> Right (Left ())
          | (op,op_pf)::rest ->
             Left ((), ((), (op, (Left ((), ((), (op_pf, (rest, ())))), ()))))),
        quaternary_ctor
          ["Coq"; "Init"; "Specif"] "existT"
          (hole_descr Descr_Constr)
          (fun _ -> hole_descr Descr_Constr)
          (fun _ _ -> Descr_Constr)
          (fun _ _ _ ->
           quaternary_ctor
             ["Coq"; "Init"; "Specif"] "existT"
             (hole_descr Descr_Constr)
             (fun _ -> hole_descr Descr_Constr)
             (fun _ _ -> Descr_Constr)
             (fun _ _ _ -> hnf_descr spec_ops_descr)
             Descr_Fail)
          (nullary_ctor
             ["Coq"; "Init"; "Datatypes"] "tt"
             Descr_Fail)))

(* Take a list of ops for a spec S and build a constr_expr of type spec_ops S.
NOTE: expects ops to be in non-reversed order. *)
let make_ops_constr_expr loc ops =
  build_constr_expr spec_ops_descr
                    (List.map (fun (op_id,_,oppred) ->
                               (mk_var (loc, field_param_id op_id),
                                match oppred with
                                | None -> mk_reference ["Coq"; "Init"; "Logic"] "I"
                                | Some _ -> mk_var (loc, field_proof_id op_id)))
                              ops)

(*
let make_ops_constr_expr loc ops =
  (List.fold_right
     (fun (op_id, op_tp, pred_opt) rest_expr ->
      mkAppC (mk_specware_ref "ops_cons",
              [mk_var (loc, field_param_id op_id);
               (match pred_opt with
                | Some _ -> mk_var (loc, field_proof_id op_id)
                | None ->
                   mkCastC (mk_reference ["Coq"; "Init"; "Logic"] "I",
                            CastConv
                              (mkAppC
                                 (mk_specware_ref "sats_op_pred",
                                  [mk_reference datatypes_mod "None";
                                   mk_hole loc]))));
               rest_expr]))
     ops
     (mkCastC (mk_reference datatypes_mod "tt",
               CastConv
                 (mkAppC (mk_specware_ref "spec_ops",
                          [mkAppC (mk_specware_ref "Spec_Axioms",
                                   [mk_hole loc])])))))
 *)

(* Take axioms for a spec S and build a constr_expr of type spec_model S ops
(where ops is implicit), assuming that a variable ax__param is in scope for each
axiom ax. NOTE: expects axioms to be in non-reversed order. *)
let rec make_model_constr_expr loc axioms =
  match axioms with
  | [] -> mk_reference ["Coq"; "Init"; "Logic"] "I"
  | [(ax_id,_)] -> mk_var (loc, field_param_id ax_id)
  | (ax_id,_)::axioms' ->
     mkAppC (mk_reference ["Coq"; "Init"; "Logic"] "conj",
             [mk_var (loc, field_param_id ax_id);
              make_model_constr_expr loc axioms'])


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
         add_to_context [mk_implicit_assum
                           (field_param_id f)
                           (mk_var (loc, field_class_id f))] in
       (* Test for an op predicate *)
       let _ =
         match pred_opt with
         | Some pred ->
            (* If there is an op predicate, add f__proof : pred to the context *)
            let _ =
              add_to_context [mk_implicit_assum (field_proof_id f) pred]
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
  (* Build the spec representation spec__Spec *)
  let _ = add_definition (loc, spec_repr_id spec.spec_name) [] None
                         (build_spec_repr loc spec) in
  (* Build spec__ops {op_params} : spec_ops spec__Spec *)
  let _ = add_definition
            (loc, spec_ops_id spec.spec_name)
            op_params
            (Some mkAppC (mk_specware_ref "spec_ops",
                          [mk_var (loc, spec_repr_id spec.spec_name)]))
            (make_ops_constr_expr loc (List.rev spec.spec_ops))
  in
  (* Build a proof spec__iso that spec__Spec is isomorphic to the spec *)
  let _ = add_term_instance
            (loc, Name spec_iso_id spec.spec_name)
            op_params
            (mkAppC (mk_specware_ref "IsoToSpecModels",
                     [mk_var (loc, spec_ops_id spec.spec_name);
                      CAppExpl
                        (loc, (None, Ident (loc, spec.spec_name), None),
                         List.rev_map (fun (op_id,_,_) ->
                                       mk_var (loc, field_param_id op_id))
                                      spec.spec_ops)]))
            (mk_named_tactic_hole
               loc
               (mk_qualid specware_mod "prove_spec_models_iso"))
  in
  (* Add all hints in the import list to the current module *)
  let _ = List.iter (fun (_, sub_imports) ->
                     List.iter (fun (_, hints) ->
                                add_typeclass_hints hints) sub_imports)
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

(* Same as above, but take in a term for a Spec representation object *)
let import_refinement_constr_expr loc constr_expr =
  (* Get the current Coq context *)
  let (evd,env) = Lemmas.get_current_context () in
  (* Internalize constr_expr into a construction *)
  let (constr,_) = Constrintern.interp_constr env evd constr_expr in
  let constr_hnf = hnf_constr constr in
  (* Destruct constr as a RefinementOf object *)
  let ((ops,axioms),_,imports) = destruct_refinementof constr_hnf in
  (* Get the source spec of the refinement in constr *)
  let src_spec_constr =
    match Term.kind_of_term constr_hnf with
    | Term.App (ctor, args) ->
       if constr_is_constructor (mk_constructor
                                   loc specware_mod "Build_RefinementOf") ctor
       then args.(0)
       else
         raise loc (Failure "import_refinement_constr_expr")
    | _ -> raise loc (Failure "import_refinement_constr_expr")
  in
  let src_spec_globref = destruct_spec_globref_constr src_spec_constr in

  (* Add all the ops specified by constr *)
  let _ =
    List.iter (fun (f,tp,oppred) ->
               add_spec_field
                 false
                 (loc, f)
                 (Constrextern.extern_constr true env evd tp)
                 (map_opt (Constrextern.extern_constr true env evd) oppred)) ops
  in
  (* Add all the axioms specified by constr *)
  let _ =
    List.iter
      (fun (ax_name,ax_tp) ->
       add_spec_field true
                      (loc, ax_name)
                      (Constrextern.extern_constr true env evd ax_tp)
                      None)
      axioms
  in

  (* The rest of this stuff runs in the context of the current spec *)
  update_current_spec
    loc
    (fun spec ->
     (* Get a fresh import number in the current spec *)
     let imp_num = find_unused_import_id spec in
     (* Add a definition spec__import<i> := constr_expr *)
     let _ = add_definition (loc, spec_import_id imp_num) [] None constr_expr in
     (* Add spec_ops__import<i> : spec_ops (ref_spec _ spec__import<i>) := ... *)
     let _ = add_definition
               (loc, spec_import_ops_id imp_num)
               []
               (Some
                  (mkAppC (mk_specware_ref "spec_ops",
                           [mkAppC (mk_specware_ref "ref_spec",
                                    [mk_hole loc;
                                     mk_var (loc, spec_import_id imp_num)])])))
               (make_ops_constr_expr loc ops) in
     (* Add spec_model__import<i> : spec_model spec_ops__import<i>
                                      (ref_spec _ spec__import<i>) := ... *)
     let _ = add_definition
               (loc, spec_import_model_id imp_num)
               (List.map (fun (ax_id,_) ->
                          mk_implicit_assum
                            (field_param_id ax_id)
                            (mk_var (loc, field_class_id ax_id))) axioms)
               (Some (mkAppC
                        (mk_specware_ref "spec_model",
                         [mkAppC (mk_specware_ref "ref_spec",
                                  [mk_hole loc;
                                   mk_var (loc, spec_import_id imp_num)]);
                          mk_var (loc, spec_import_ops_id imp_num)])))
               (make_model_constr_expr loc axioms) in

     (* Get the Coq context again (cause we added some defs) *)
     let (evd,env) = Lemmas.get_current_context () in
     let evdref = ref evd in
     (* Interpret the value of spec_ops__import<i> to a constr *)
     let ops_constr =
       hnf_constr
         (fst (Constrintern.interp_constr
                 env evd (mk_var (loc, spec_import_ops_id imp_num))))
     in

     (* Helper function for replacing free variables f__param or f__proof with
     the hole (_:f__class) or (_:<type of f proofs>), respectively *)
     let field_var_type_map =
       List.fold_left
         (fun map (op_id, op_tp, oppred) ->
          let map1 = Id.Map.add
                       (field_param_id op_id)
                       (Glob_term.GRef
                          (loc,
                           (* FIXME HERE NOW: the following global reference is
                           causing a Not_found exception when it is printed! *)
                           (try Nametab.locate
                                  (* (mk_qualid ["Specware"; "Spec"] "Spec") *)
                                  (qualid_of_ident (field_class_id op_id))
                            with Not_found ->
                              raise dummy_loc
                                    (Failure "import_refinement_constr_expr")),
                           None))
                       map
          in
          match oppred with
          | None -> map1
          | Some pred ->
             Id.Map.add (field_proof_id op_id)
                        (Detyping.detype true [] env !evdref pred)
                        map1
         )
         Id.Map.empty ops
     in
     let replace_vars_by_holes =
       map_rec_glob_constr_with_binders
         (function
           | Name x -> Id.Map.remove x
           | Anonymous -> fun map -> map)
         (fun map g ->
          match g with
          | (Glob_term.GVar (loc, x) | Glob_term.GRef (loc, VarRef x, _)) as glob ->
             (try mk_glob_cast loc (mk_glob_hole loc) (Id.Map.find x map)
              with
              | Not_found -> glob)
          | glob -> glob)
         field_var_type_map
     in

     (* For each import, get a reference to the imported spec, and also generate
     hints for building its ops *)
     let import_refs_and_hints =
       List.map
         (fun refimp ->
          (* Look up the spec structure *)
          let imp_spec = lookup_global_spec refimp.ref_import_fromspec in
          let imp_spec_locref =
            spec_globref_to_locref refimp.ref_import_fromspec in

          (* Normalize the term (map_ops interp spec_ops__import<i>) to get the
          ops of imp_spec in terms of the ops of the current spec *)
          let imp_ops_constr =
            destruct_constr
              spec_ops_descr
              (compute_constr
                 (Term.mkApp
                    (Term.mkConst (mk_constant loc specware_mod "map_ops"),
                     [| Term.mkConst (global_spec_repr_constant
                                        loc refimp.ref_import_fromspec);
                        Term.mkApp
                          (Term.mkConst (mk_constant loc specware_mod "ref_spec"),
                           [| Term.mkConst (global_spec_repr_constant
                                              loc src_spec_globref);
                              Term.mkVar (spec_import_id imp_num) |]);
                        refimp.ref_import_interp;
                        ops_constr |])))
          in

          (* Build the hint "Hint Extern 1 op__class => refine (opexpr_repl)"
          for each op in imp_spec, where opexpr_repl has holes in place of the
          f__param variables of the current spec *)
          let hints =
            List.map2
              (fun (op_id, _, oppred) (opexpr_constr, _) ->
               (* Detype opexpr, since tactics take untyped glob_terms *)
               let opexpr =
                 Detyping.detype true [] env !evdref opexpr_constr
               in
               (* Replace each free var f__param of opexpr with (_:f__class) *)
               let opexpr_repl = replace_vars_by_holes opexpr in
               (* Now build the hint *)
               let tacexpr =
                 (Tacexpr.TacML
                    (loc,
                     {Tacexpr.mltac_tactic = "refine";
                      Tacexpr.mltac_plugin = "extratactics"},
                     [Genarg.in_gen
                        (Genarg.glbwit Constrarg.wit_constr)
                        (opexpr_repl, None)]
                     (* [] *)
                 ))
                 (*
                 (Tacexpr.TacArg
                    (loc,
                     Tacexpr.TacCall
                       (loc, ArgArg (loc, Nametab.locate_tactic
                                            (qualid_of_ident (Id.of_string "refine"))),
                        [Tacexpr.ConstrMayEval
                           (ConstrTerm (opexpr_repl, None))]
                          (* [] *)
                 ))) *)
               in
               let _ = debug_printf 1 "@[hint tactic: %a@]\n"
                                    pp_autotactic (Hints.Extern tacexpr) in
               Hints.HintsExternEntry
                 (1,
                  Some ([], Pattern.PRef
                              (try Nametab.locate
                                     (field_in_spec imp_spec_locref
                                                    (field_class_id op_id))
                               with Not_found ->
                                 raise dummy_loc
                                       (Failure "import_refinement_constr_expr"))),
                  tacexpr))
              (List.rev imp_spec.spec_ops) imp_ops_constr
          in

          (* Now add all the hints to the typeclass_instances database *)
          let _ = add_typeclass_hints hints in

          (* FIXME HERE NOW: add the instance *)
          (refimp.ref_import_fromspec, hints)
         )
         imports
     in

     (* Add the import list to the currernt spec *)
     {spec with spec_imports = spec.spec_imports @ [imp_num, import_refs_and_hints]})


(***
 *** Additions to the Coq parser
 ***)

(* Run f, catching any exceptions and turning them into user_errors *)
(* FIXME: actually write this! *)
let reporting_exceptions f =
  try f ()
  with
  | MalformedRefinement (constr, tag, sub_constr) ->
     user_err_loc (dummy_loc, "_",
                   str "Malformed refinement term "
                   ++ brk (0,0)
                   ++ Printer.pr_constr constr
                   ++ brk (0,0)
                   ++ str (": could not parse " ^ tag ^ " in subterm ")
                   ++ brk (0,0)
                   ++ Printer.pr_constr sub_constr)

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
