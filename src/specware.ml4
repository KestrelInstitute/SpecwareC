(* Copyright (c) 2015, Kestrel Institute
All rights reserved.

This program is free software; you can redistribute it and/or modify it under
the terms of the included LICENSE.txt file.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the LICENSE.txt for more details. *)

DECLARE PLUGIN "specware_c_plugin"

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

(* Test if an id has the form f__param, returning f if so *)
let match_param_id id = Option.map Id.of_string (match_suffix id "__param")

(* Build the identifier used to quantify over the proof of a field's oppred as a
   local variable *)
let field_proof_param_id f = add_suffix f "proof__param"

(* Get the identifier used for the underlying variable of a defined op *)
let field_var_id f = add_suffix f "var"

(* Get the identifier used locally for the type of a field *)
let field_type_id f = add_suffix f "type"

(* Get the identifier used locally for the type-class of a field *)
let field_class_id f = add_suffix f "class"

(* Get the identifier used for a field predicate *)
let field_pred_id f = add_suffix f "pred"

(* Get the identifier used for the proof of a field predicate *)
let field_proof_id f = add_suffix f "proof"

(* Test if an id has the form f__proof, returning f if so *)
let match_proof_id id = Option.map Id.of_string (match_suffix id "__proof")

(* Test if an id has the form f__proof__param, returning f if so *)
let match_proof_param_id id =
  Option.map Id.of_string (match_suffix id "__proof__param")

(* The name of the instance associated with a field *)
let field_inst_id f = add_suffix f "inst"

(* The name of the record field associated with spec field named f *)
let field_recfield_id f = add_suffix f "field"

(* The name of the Spec representation of a spec named s_id *)
let spec_repr_id s_id = add_suffix s_id "Spec"

(* The name of the typeclass field in the record type of a spec named s_id *)
let spec_proofs_id s_id = add_suffix s_id "proofs"

(* The name of the record type of a spec named s_id *)
let spec_rectp_id s_id = add_suffix s_id "Record"

(* The name of the constructor for the record type of a spec named s_id *)
let spec_recctor_id s_id = Nameops.add_prefix "Build_" (spec_rectp_id s_id)

(* The name of the SpecCtor for a spec named s_id *)
let spec_ctor_id s_id = add_suffix s_id "ctor"

(* The name of the parameteric model constructor for a spec named s_id *)
let spec_model_id s_id = add_suffix s_id "model"

(* The name of the IsoToSpec proof for a spec named s_id *)
let spec_iso_id s_id = add_suffix s_id "Iso"

(* Get the Id for the interpretation for import number i *)
let spec_import_id i =
  add_suffix (Id.of_string "spec") ("import" ^ string_of_int i)

(* The Id for the record type of a spec *)
let spec_record_id spec_id =
  add_suffix spec_id "Record"

(* Get the Id for the spec_model for import number i *)
let spec_import_model_id i =
  add_suffix (Id.of_string "spec_model") ("import" ^ string_of_int i)

(* Get the Id for the interppretation for import number i *)
let spec_import_model_id i =
  add_suffix (Id.of_string "spec_model") ("import" ^ string_of_int i)

(* Get the Id for the jth interpretation in the ith import *)
let spec_import_interp_id i j =
  add_suffix
    (add_suffix (Id.of_string "spec") ("import" ^ string_of_int i))
    ("interp" ^ string_of_int j)

(* Get the Id for the jth instance generated from the ith import *)
let spec_import_instance_id i j =
  add_suffix
    (add_suffix (Id.of_string "spec") ("import" ^ string_of_int i))
    ("instance" ^ string_of_int j)


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

(* Return a local reference to the Build_ constructor of the spec typeclass of a
spec given by local reference *)
let spec_typeclass_builder_qualid locref =
  field_in_spec locref
                (Id.of_string
                   ("Build_" ^ Id.to_string (spec_locref_basename locref)))

(* Return a local reference to the Spec object for a spec *)
let spec_repr_qualid locref =
  qualid_cons locref (spec_repr_id (spec_locref_basename locref))

let spec_repr_ref (loc, locref) =
  Qualid (loc, spec_repr_qualid locref)

let spec_iso_qualid locref =
  qualid_cons locref (spec_iso_id (spec_locref_basename locref))

let spec_iso_ref loc locref =
  Qualid (loc, spec_iso_qualid locref)

let spec_model_ref loc locref =
  Qualid (loc, qualid_cons locref (spec_model_id (spec_locref_basename locref)))

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
  try Nametab.shortest_qualid_of_module spec_globref
  with Not_found ->
    raise dummy_loc (Failure "spec_globref_to_locref")

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
  spec_repr_ref (loc, spec_globref_to_locref globref)

let global_spec_iso_ref loc globref =
  spec_iso_ref loc (spec_globref_to_locref globref)

(* Extract the name of a spec as an Id.t from a spec_globref *)
let spec_globref_basename globref =
  spec_locref_basename (spec_globref_to_locref globref)

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

(* A spec_field is a field name plus its type, which can be either a constr or a
constr_expr *)
type 'a spec_field = {field_id: Id.t;
                      field_type: 'a}
type expr_spec_field = constr_expr spec_field
type constr_spec_field = Constr.t spec_field

let spec_field_class_id specf = field_class_id specf.field_id
let spec_field_param_id specf = field_param_id specf.field_id
let spec_field_param_var loc specf = mk_var (loc, spec_field_param_id specf)

(* Build a parameter / assumption for a spec_field *)
let param_of_spec_field ?(implicit=true) loc specf =
  (if implicit then mk_implicit_assum else mk_explicit_assum)
    (spec_field_param_id specf)
    (mk_var (loc, spec_field_class_id specf))

(* Build a record field for a spec_field *)
let recfield_of_spec_field loc coercion_p specf =
  ((loc, field_recfield_id specf.field_id),
   mk_var (loc, spec_field_class_id specf),
   coercion_p)

(* A spec contains its name, its module path, its ops, its axioms, and its
imports. Note that ops and axioms --- collectively called the "fields" of the
spec --- are stored in reverse order, for efficiency of adding new ones. *)
type spec = {
  spec_name: Id.t;
  spec_globref: spec_globref;
  spec_ops: expr_spec_field list;
  spec_axioms: expr_spec_field list;
  spec_imports: spec_import list
}
 and spec_import = {
   spec_import_num: int;
   spec_import_spec: spec;
   spec_import_globref: spec_globref;
   spec_import_type: constr_expr
 }

(* Build the expression "binder (f__param:T), body" where "binder" is "forall"
when as_type is true and "lambda" when as_type is false.  When the type T has
the form "f__param = M" for some variable f__param and term M, also add a let
expression "let f := M" around body.  NOTE: T here does not use the op
type-classes, i.e., we are assuming we are not "in the spec". *)
(*
let abstract_field loc as_type f body : constr_expr =
  let full_body =
    match 
 with
    | Pred_Eq eq_expr ->
       mkLetInC ((loc, Name op_id), eq_expr, body)
    | _ -> body
  in
  (if as_type then mkCProdN else mkCLambdaN)
    loc
    (LocalRawAssum ([loc, Name (field_param_id op_id)],
                    Default Explicit, op_tp)
     ::(if oppred_is_nontrivial oppred then
          [LocalRawAssum ([loc, Name (field_proof_param_id op_id)],
                          Default Explicit, op_pred_expr ~in_spec:false loc op)]
        else []))
    full_body

(* The plural of abstract_op, above, with as_type=true *)
let forall_ops loc (ops : constr_expr op list) body : constr_expr =
  List.fold_right (abstract_op loc true) ops body

(* The plural of abstract_op, above, with as_type=false *)
let lambda_ops loc (ops : constr_expr op list) body : constr_expr =
  List.fold_right (abstract_op loc false) ops body
 *)

(* Create an empty spec with the given name in the current module *)
let make_empty_spec spec_id spec_globref =
  { spec_name = spec_id; spec_globref = spec_globref;
    spec_ops = []; spec_axioms = []; spec_imports = [] }

(* Whether spec contains an op or axiom named id *)
let contains_field spec id =
  List.exists (fun specf -> Id.equal id specf.field_id) spec.spec_ops ||
    List.exists (fun specf -> Id.equal id specf.field_id) spec.spec_axioms

(* Build a spec_field from a spec_import *)
let spec_field_of_import imp =
  {field_id = spec_import_id imp.spec_import_num;
   field_type = imp.spec_import_type}

(* Return the imports of spec as spec_fields *)
let spec_import_fields spec =
  List.map spec_field_of_import spec.spec_imports

(* Find an unused import number in spec *)
let find_unused_import_id spec = List.length spec.spec_imports

(* Find all the __param implicit arguments on which an id depends *)
let field_param_deps id =
  let gr = Nametab.locate (qualid_of_ident id) in
  (* FIXME: this just checks if an implicit argument name is of the form
  f__param for some existing field f; maybe this should be more subtle...? *)
  List.filter
    (fun id ->
     match match_param_id id with
     | Some f ->
        (try Nametab.exists_cci
               (Nametab.full_name_cci (qualid_of_ident f))
         with Not_found -> false)
     | None -> false)
    (implicit_arg_ids gr)

(* Build an expression for the typeclass of spec applied to named parameters *)
let spec_typeclass_expr_params loc spec =
  mk_ref_app_named_args
    loc
    (global_spec_typeclass_ref loc spec.spec_globref)
    (List.rev_map (fun opf ->
                   (spec_field_param_id opf,
                    mk_var (loc, spec_field_param_id opf)))
                  spec.spec_ops)


(***
 *** Exceptions
 ***)

(* There is no current spec *)
exception NoCurrentSpec

(* There is no registered spec with the given name *)
exception NoSuchSpec of spec_globref

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Field already exists in the current spec *)
exception FieldExists of Id.t

(* Attempt to add an op when axioms have already been declared *)
exception AxiomsExist

(* MalformedSpec (spec_c,tag,sub_c): error parsing sub-component sub_c as a tag
object in the Spec object spec_c *)
exception MalformedSpec of Constr.t * string * Constr.t

(* MalformedRefinement (ref_c,tag,sub_c): error parsing sub-component sub_c as a tag
object in the RefinementOf object ref_c *)
exception MalformedRefinement of Constr.t * string * Constr.t

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
  | DescrFailed (tag, constr) ->
     user_err_loc (dummy_loc, "_",
                   str ("Could not parse " ^ tag ^ " in ")
                   ++ brk (0,0)
                   ++ Printer.pr_constr constr)


(***
 *** Global registration of specs
 ***)

(* The global table of registered specs, by spec global ref *)
let spec_table = Summary.ref ~name:"spec_table" (MPmap.empty)

(* Add a reference to the spec_table *)
let add_specref specref =
  spec_table := MPmap.add (!specref).spec_globref specref !spec_table

(* Constructor for persistent references to spec objects *)
let inSpec =
  Libobject.declare_object
    {(Libobject.default_object "SPEC") with
      Libobject.cache_function =
        (fun (_,specref) -> add_specref specref);
      Libobject.load_function = (fun _ (_,specref) -> add_specref specref);
      Libobject.open_function = (fun _ (_,specref) -> add_specref specref);
      Libobject.discharge_function = (fun (_,specref) -> Some specref);
      Libobject.classify_function = (fun specref -> Libobject.Keep specref)
    }

(* Declare a module to be a spec *)
let declare_spec globref spec_id =
  Lib.add_anonymous_leaf (inSpec (ref (make_empty_spec spec_id globref)))

(* Look up a mutable spec object from a global reference to it *)
let lookup_global_spec_ref globref =
  try MPmap.find globref !spec_table
  with Not_found as e ->
    raise dummy_loc (NoSuchSpec globref)

let lookup_global_spec globref =
  !(lookup_global_spec_ref globref)

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

(* A description of the SpecAxiom type *)
let spec_axiom_descr : (constr_spec_field, expr_spec_field) constr_descr =
  Descr_Iso
    ("SpecAxiom",
     (function
       | Left (f, (tp, ())) -> {field_id = f; field_type = tp}
       | Right emp -> emp.elim_empty),
     (fun specf -> Left (specf.field_id, (specf.field_type, ()))),
     binary_ctor
       specware_mod "specAxiom" id_descr (fun _ -> Descr_Constr) Descr_Fail)

(* The description of a list of axioms *)
let axiom_list_descr : (constr_spec_field list,
                        expr_spec_field list) constr_descr =
  list_descr spec_axiom_descr

(* The description of the Spec inductive type as lists of ops and axioms *)
let spec_descr : (constr_spec_field list * constr_spec_field list,
                  expr_spec_field list * expr_spec_field list) constr_descr =
  Descr_Rec
    (fun spec_descr ->
     Descr_Iso
       ("Spec",
        (function
          | Left (f, (tp, ((ops, axioms), ()))) ->
             ({field_id = f; field_type = tp}::ops, axioms)
          | Right (Left (axioms, ())) -> ([], axioms)
          | Right (Right emp) -> emp.elim_empty),
        (function
          | (specf::ops', axioms) ->
             Left (specf.field_id, (specf.field_type, ((ops', axioms), ())))
          | ([], axioms) -> Right (Left (axioms, ()))),
        ternary_ctor
          specware_mod "Spec_Cons"
          (hnf_descr id_descr) (fun _ -> Descr_Constr)
          (fun f_sum _ ->
           let f = match f_sum with Left f -> f | Right f -> f in
           Descr_ConstrMap
             ((fun rest_constr ->
               let rest_body_constr =
                 Reduction.beta_appvect
                   rest_constr [| Term.mkVar (field_param_id f) |] in
               hnf_constr rest_body_constr),
              (fun rest_expr ->
               (* Make a lambda expression for the rest argument of Spec_Cons.
               The expression class_expr is an application of f__class to all of
               its implicit arguments corresponding to fields in the current
               spec. *)
               let class_expr =
                 mk_id_app_named_args dummy_loc (field_class_id f)
                                      (List.map
                                         (fun id -> (id, mk_var (dummy_loc, id)))
                                         (field_param_deps (field_class_id f)))
               in
               (mkCLambdaN
                  dummy_loc
                  [LocalRawAssum ([dummy_loc, Name (field_param_id f)],
                                  Default Explicit, class_expr)]
                  rest_expr)),
              spec_descr))
          (unary_ctor
             specware_mod "Spec_Axioms" (hnf_descr axiom_list_descr)
             Descr_Fail)))

(* Build a constr of type Spec that represents a spec; we don't use constr_expr
since we have to do some unfolding and we don't want to extern the resulting
constr to constr_expr just to intern it back to constr again *)
let build_spec_repr loc spec : Constr.t Evd.in_evar_universe_context =
  (* Get the current Coq context *)
  let (evd,env) = Lemmas.get_current_context () in
  (* Build the constr_expr the represents the spec *)
  let spec_expr =
    build_constr_expr spec_descr
                      (List.rev spec.spec_ops,
                       List.rev (spec_import_fields spec @ spec.spec_axioms)) in
  let _ = debug_printf 1 "@[build_spec_repr (1):@ %a@]\n"
                       pp_constr_expr spec_expr in
  (* Internalize spec_expr into a construction *)
  let (constr,uctx) = Constrintern.interp_constr env evd spec_expr in
  let _ = debug_printf 1 "@[build_spec_repr (2):@ %a@]\n"
                       pp_constr constr in

  (* Helper definitions *)
  let consop_constructor = mk_constructor specware_mod "Spec_Cons" in
  let axioms_constructor = mk_constructor specware_mod "Spec_Axioms" in
  (* Helper: unfold constants in constr that are in const_set *)
  let rec unfold_helper const_set constr =
    let unfold_const_app const args =
      if Cset.mem (fst const) const_set then
        (* NOTE: the value of const could still require unfolding *)
        let const_unfolded =
          unfold_helper const_set (Environ.constant_value_in env const) in
        Reduction.beta_appvect const_unfolded args
      else
        Constr.map (unfold_helper const_set) constr
    in
    match Term.kind_of_term constr with
    | Term.Const const ->
       unfold_const_app const [| |]
    | Term.App (head, args)
         when Term.isConst head ->
       let const = Term.destConst head in
       unfold_const_app const (Array.map (unfold_helper const_set) args)
    | _ -> Constr.map (unfold_helper const_set) constr
  in
  (* Helper to add ids to a const_set *)
  let const_set_add id const_set =
    let const = Nametab.locate_constant (qualid_of_ident id) in
    Cset.add const const_set
  in
  (* Helper: unfold all the constant definitions in a Spec *)
  let rec unfold_spec_repr const_set ops constr =
    match Term.kind_of_term constr, ops with
    | Term.App (head, args), []
         when constr_is_constructor axioms_constructor head ->
       (* For the base case, only axioms remaining, just recursively unfold,
       since we are not going to add any more ops *)
       Term.mkApp (head, Array.map (unfold_helper const_set) args)
    | Term.App (head, [| f_c; tp_c; rest_c |]), opf::ops'
         when constr_is_constructor consop_constructor head ->
       (* In the cons case, first check that the field id is correct *)
       let _ =
         if not (Id.equal opf.field_id (destruct_constr id_descr f_c)) then
           raise loc (Failure "unfold_spec_repr")
       in
       (* Next, destruct the rest lambda *)
       let (rest_nm,rest_tp,rest_body) =
         match Term.decompose_lam_n 1 rest_c with
         | ((nm,tp)::[], body) -> (nm,tp,body)
         | _ -> raise loc (Failure "unfold_rest_fun")
       in
       (* Now re-form the lambda, unfolding the type and recursing in body *)
       let rest' =
         Term.mkLambda
           (rest_nm,
            unfold_helper const_set rest_tp,
            (unfold_spec_repr
               (* In rest_body, also unfold field_id and its class *)
               (const_set_add
                  opf.field_id
                  (const_set_add (spec_field_class_id opf) const_set))
               ops'
               rest_body))
       in
       (* Finally, re-form the whole application *)
       Term.mkApp (head,
                   [| unfold_helper const_set f_c;
                      unfold_helper const_set tp_c;
                      rest' |])
    | _ -> raise loc (Failure "unfold_spec_repr")
  in

  (* Apply the unfold_spec_repr helper to constr *)
  let constr_unfolded =
    unfold_spec_repr Cset.empty (List.rev spec.spec_ops) constr in
  let _ = debug_printf 1 "@[build_spec_repr (3):@ %a@]\n"
                       pp_constr constr_unfolded in
  (constr_unfolded, uctx)


(***
 *** Inductive Descriptions of Models
 ***)

(*
(* A description of the spec_model S type for arbitrary spec S. *)
let spec_model_descr ?(env_opt=None) ?(evdref_opt=None) ()
    : ((Constr.t * Constr.t) list * Constr.t,
       (constr_expr op * constr_expr * constr_expr) list
       * constr_expr) constr_descr =
  Descr_Rec
    (fun spec_model_descr ->
     Descr_Iso
       ("spec_model",
        (function
          | Left (_, (_, (_, (x1, (x2, (x3, ())))))) ->
             ((x1,x2)::(fst x3), snd x3)
          | Right x -> ([], x)),
        (function
          | ([], x) -> Right x
          | (((op_id,op_tp,oppred), op_expr, op_pf)::rest, x) ->
             Left ((), (build_constr_expr (oppred_descr op_id) (op_tp,oppred),
                        ((), (op_expr, (op_pf, ((rest, x), ()))))))),
        senary_ctor
          specware_mod "opCons"
          (hole_descr Descr_Constr)
          (fun _ -> Descr_Constr)
          (fun _ _ -> hole_descr Descr_Constr)
          (fun _ _ _ -> Descr_Constr)
          (fun _ _ _ _ -> Descr_Constr)
          (fun _ _ _ _ _ -> hnf_descr ~env_opt ~evdref_opt spec_model_descr)
          Descr_Constr))

(* Take a list of ops and axiom names for some unspecified spec S and build a
constr_expr of type spec_model S using f__param and f__proof__param free
variables. NOTE: expects ops and axioms to be in non-reversed order. *)
let make_model_constr_expr loc ops ax_ids =
  let rec ax_helper ax_ids =
    match ax_ids with
    | [] -> mk_reference ["Coq"; "Init"; "Logic"] "I"
    | [ax_id] -> mk_var (loc, field_param_id ax_id)
    | ax_id::ax_ids' ->
       mkAppC (mk_reference ["Coq"; "Init"; "Logic"] "conj",
               [mk_var (loc, field_param_id ax_id); ax_helper ax_ids'])
  in
  build_constr_expr
    (spec_model_descr ())
    (List.map (fun op ->
               let (op_id,_,oppred) = op in
               (op, mk_var (loc, field_param_id op_id),
                match oppred with
                | Pred_Trivial -> mk_reference ["Coq"; "Init"; "Logic"] "I"
                | _ -> mk_var (loc, field_proof_param_id op_id)))
              ops,
     ax_helper ax_ids)


(* This describes a spec_model, which is a right-nested series of conj's, or the
single term I (proof of True) for the empty model, or a single proof for the
singleton list. *)
let spec_model_descr : (Constr.t list, constr_expr list) constr_descr =
  Descr_Rec
    (fun spec_model_descr ->
     Descr_Iso
       ("spec_model",
        (function
          | Left (_, (_, (x1, (x2, ())))) -> x1::x2
          | Right (Left ()) -> []
          | Right (Right x1) -> [x1]),
        (function
          | [] -> Right (Left ())
          | [pf] -> Right (Right pf)
          | pf::rest -> Left ((), ((), (pf, (rest, ()))))),
        quaternary_ctor
          ["Coq"; "Init"; "Logic"] "conj"
          (hole_descr Descr_Constr)
          (fun _ -> hole_descr Descr_Constr)
          (fun _ _ -> Descr_Constr)
          (fun _ _ _ -> spec_model_descr)
          (nullary_ctor
             ["Coq"; "Init"; "Logic"] "I"
             Descr_Constr)))


(* Take axioms for a spec S and build a constr_expr of type spec_model S ops
(where ops is implicit), assuming that a variable ax__param is in scope for each
axiom ax. NOTE: expects axioms to be in non-reversed order. *)
let rec make_model_constr_expr loc axioms =
  build_constr_expr spec_model_descr
                    (List.map (fun (ax_id, _) ->
                               mk_var (loc, field_param_id ax_id)) axioms)
(*
  match axioms with
  | [] -> mk_reference ["Coq"; "Init"; "Logic"] "I"
  | [(ax_id,_)] -> 
  | (ax_id,_)::axioms' ->
     mkAppC (mk_reference ["Coq"; "Init"; "Logic"] "conj",
             [mk_var (loc, field_param_id ax_id);
              make_model_constr_expr loc axioms'])
 *)
 *)


(***
 *** Building Up the Current Spec
 ***)

(* Get the current spec, raising an exception if there is none *)
let get_current_spec loc =
  try lookup_global_spec (Lib.current_mp ())
  with NoSuchSpec _ ->
    raise loc NoCurrentSpec

(* Update the current spec, if it exists, by applying f *)
let update_current_spec loc f =
  try
    let specref = lookup_global_spec_ref (Lib.current_mp ()) in
    specref := f !specref
  with NoSuchSpec _ ->
    raise loc NoCurrentSpec

(* Add a field (op or axiom) to the current spec *)
let add_spec_field ?(err_on_exists=true) axiom_p lid tp =
  (* Extract the field id and loc from field_name *)
  let f = located_elem lid in
  let loc = located_loc lid in
  let specf = {field_id = f; field_type = tp} in

  update_current_spec
    loc
    (fun spec ->
     (* First, check that the given field name does not already exist *)
     if contains_field spec f then
       if err_on_exists then raise loc (FieldExists f)
       else spec
     else

       (* Check that we are not adding an op when axioms are present *)
       let _ =
         match axiom_p, spec.spec_axioms with
         | false, _::_ -> raise loc AxiomsExist
         | _ -> ()
       in

       (* Add the operational type-class f__class := acc : tp *)
       let _ = add_typeclass (loc, field_class_id f) true axiom_p []
                             [((loc, f), tp, false)]
       in

       (* Add an instance of the type-class to the context *)
       let _ =
         add_to_context [mk_implicit_assum
                           (field_param_id f)
                           (mk_var (loc, field_class_id f))]
       in

       (* Then, finally, add the field to the current spec *)
       if axiom_p then
         { spec with spec_axioms = specf::spec.spec_axioms }
       else
         { spec with spec_ops = specf::spec.spec_ops }
    )


(* Add an import to the current spec, given by a reference *)
let add_spec_import r =
  let (loc, locref) = qualid_of_reference r in
  let (spec, globref) = lookup_spec_and_globref locref in

  (* Build the type of the import, which is the import's typeclass applied to
  all of its ops *)
  let import_tp = spec_typeclass_expr_params loc spec in

  (* Add all the ops of the imported spec that are not already present *)
  let _ = List.iter
            (fun specf ->
             add_spec_field ~err_on_exists:false false
                            (loc, specf.field_id) specf.field_type)
            (List.rev spec.spec_ops)
  in

  (* Finally, add the import *)
  update_current_spec
    loc
    (fun spec ->
     let imp_num = find_unused_import_id spec in
     let imp = {spec_import_num = imp_num;
                spec_import_spec = spec;
                spec_import_globref = globref;
                spec_import_type = import_tp} in

     {spec with spec_imports = imp::spec.spec_imports}
    )


(***
 *** Spec Translations
 ***)

(* A spec translation specifies a map on identifiers *)
type spec_translation_elem =
  (* Map a single name to another *)
  | XlateSingle of Id.t * Id.t
  (* Map all names with a given prefix to instead use a different prefix *)
  | XlatePrefix of string * string

type spec_translation = spec_translation_elem list

(* Translate an id using a single translation_elem, returning None if the
translation_elem had no effect; same as translate_id1 in Spec.v *)
let translate_id1 xlate_elem f =
  match xlate_elem with
  | XlateSingle (f_from, f_to) ->
     if Id.equal f f_from then
       Some f_to
     else None
  | XlatePrefix (from_prefix, to_prefix) ->
     (match match_prefix f from_prefix with
      | None -> None
      | Some f_suf -> Some (Id.of_string (to_prefix ^ f_suf)))

(* Translate an id; this is the same as translate_id in Spec.v *)
let rec translate_id xlate f =
  match xlate with
  | [] -> f
  | elem::xlate' ->
     (match translate_id1 elem f with
      | None -> translate_id xlate' f
      | Some res -> res)


(***
 *** Interpretations
 ***)

(* Mappings from names in a domain spec to names or terms in a codomain spec *)
type interp_map_elem =
  (* Map a name to another name using a spec translation *)
  | InterpMapXlate of Loc.t * spec_translation_elem
  (* Map a name to an expression *)
  | InterpMapTerm of Id.t * constr_expr
type interp_map = interp_map_elem list

(* Apply an interp_map to an identifier, returning None if the identifier is not
explicitly mapped to a term *)
let rec apply_interp_map interp_map f =
  match interp_map with
  | [] -> None
  | (InterpMapXlate (xloc, xelem))::interp_map' ->
     (match translate_id1 xelem f with
      | Some f' -> Some (mk_var (xloc, f'))
      | None -> apply_interp_map interp_map' f)
  | (InterpMapTerm (f_from, expr_to))::interp_map' ->
     if Id.equal f f_from then Some expr_to else
       apply_interp_map interp_map' f

(* Build an expression that maps from the record type of codom_globref to that
of dom_globref, mapping fields in dom_globref using interp_map *)
let make_interp_expr loc dom_globref codom_globref interp_map =
  let dom_spec = lookup_global_spec dom_globref in
  let dom_locref = spec_globref_to_locref dom_globref in
  let codom_spec = lookup_global_spec codom_globref in
  let codom_locref = spec_globref_to_locref codom_globref in
  let lname_of_specf specf = (loc, Name specf.field_id) in
  mkCLambdaN
    loc
    [LocalRawAssum ([loc, Name (Id.of_string "__r")],
                    Default Explicit, mk_hole loc)]
    (CLetTuple
       (loc,
        List.rev_map lname_of_specf codom_spec.spec_ops
        @ [loc, Name (spec_proofs_id codom_spec.spec_name)],
        (None, None),
        mk_var (loc, Id.of_string "__r"),
        (CLetTuple
           (loc,
            List.rev_map
              lname_of_specf
              (spec_import_fields codom_spec @ codom_spec.spec_axioms),
            (None, None),
            mk_var (loc, spec_proofs_id dom_spec.spec_name),
            (CRecord
               (loc, None,
                List.rev_map
                  (fun specf ->
                   let t =
                     match apply_interp_map interp_map specf.field_id with
                     | Some t -> t
                     | None ->
                        if List.exists (fun specf' ->
                                        Id.equal specf.field_id specf'.field_id)
                                       codom_spec.spec_ops
                        then
                          mk_var (loc, specf.field_id)
                        else
                          mk_hole loc
                   in
                   (Qualid (loc, field_in_spec dom_locref specf.field_id), t))
                  dom_spec.spec_ops
                @ [Qualid (loc,
                           field_in_spec dom_locref
                                         (spec_proofs_id dom_spec.spec_name)),
                   (* FIXME HERE: try to fill out the proofs as well *)
                   mk_hole loc]))
    ))))


(***
 *** Spec Terms
 ***)

(* A spec term is shorthand for refinements involving named specs, translations,
and spec substitutions *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * spec_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * constr_expr
  (* A spec substitution with a translation applied to the interpretation *)
  | SpecSubstXlate of spec_term * constr_expr * spec_translation
  (* Adding definitions to ops in a spec *)
  (* | SpecAddDefs of spec_term * Loc.t * (lident * Constrexpr.constr_expr) list *)

(* Build a RefinementOf expr from a spec_term *)
(*
let refinement_expr_of_spec_term st =
  let rec helper st =
    match st with
    | SpecRef r ->
       mkAppC (mk_specware_ref "id_refinement",
               [mkRefC (spec_repr_ref (qualid_of_reference r))])
    | SpecXlate (st', xlate) ->
       let ref_expr' = helper st' in
       mkAppC (mk_specware_ref "refinement_translate",
               [ref_expr'; build_constr_expr spec_translation_descr xlate])
    | SpecSubst (st', interp_expr) ->
       let ref_expr' = helper st' in
       mkAppC (mk_specware_ref "refinement_subst",
               [ref_expr'; interp_expr;
                mk_named_tactic_hole (constr_loc interp_expr)
                                     (mk_qualid specware_mod "prove_spec_overlap")])
    | SpecSubstXlate (st', interp_expr, xlate) ->
       let ref_expr' = helper st' in
       mkAppC (mk_specware_ref "refinement_subst_xlate",
               [ref_expr'; interp_expr;
                build_constr_expr spec_translation_descr xlate;
                mk_named_tactic_hole (constr_loc interp_expr)
                                     (mk_qualid specware_mod "prove_spec_overlap")])
  in
  (* FIXME: need to remove existing ops and axioms from an imported spec *)
  helper st
 *)

(* Import a spec_term *)
let import_spec_term loc st =
  raise loc (Failure "import_spec_term")


(***
 *** Beginning and Ending the Current Spec
 ***)

(* Complete the current spec, by creating its axiom type-class, registering it
   in the global spec table, and creating representation as a Spec object. NOTE:
   this needs to be called after the spec's section is closed, but before its
   module is closed. *)
let complete_spec loc spec =

  (* Build parameters for all the ops and the axioms, where the latter include
  all the imports as well *)
  let op_params = List.rev_map (param_of_spec_field loc) spec.spec_ops in
  let all_axioms = spec_import_fields spec @ spec.spec_axioms in
  let ax_params = List.rev_map (param_of_spec_field loc) all_axioms in

  (* Create the spec typeclass *)
  let _ = add_typeclass
            (loc, spec.spec_name) false true op_params
            (List.rev_map (recfield_of_spec_field loc true) all_axioms)
  in

  (* Create the record type spec__Record *)
  let _ =
    add_record_type
      (loc, spec_rectp_id spec.spec_name) (Some type_expr) []
      (List.rev_map (recfield_of_spec_field loc false) spec.spec_ops
       @ [(loc, spec_proofs_id spec.spec_name),
          mk_id_app_named_args
            loc spec.spec_name
            (List.rev_map (fun specf ->
                           (spec_field_param_id specf,
                            mk_var (loc, field_recfield_id specf.field_id)))
                          spec.spec_ops),
          false])
  in

  (* Build the spec representation spec__Spec *)
  let _ = add_definition_constr (spec_repr_id spec.spec_name) None
                                (build_spec_repr loc spec) in

  (* Build the SpecCtor for spec *)
  let _ =
    add_definition
      (loc, spec_ctor_id spec.spec_name)
      []
      (Some (mkAppC (mk_specware_ref "SpecCtor",
                     [mk_var (loc, spec_rectp_id spec.spec_name);
                      mk_var (loc, spec_repr_id spec.spec_name)])))
      (mkCLambdaN
         loc
         (List.rev_map (param_of_spec_field ~implicit:false loc)
                       (all_axioms @ spec.spec_ops))
         (mkAppC
            (mk_var (loc, spec_recctor_id spec.spec_name),
             List.rev_map (spec_field_param_var loc) spec.spec_ops
             @ [mkAppC
                  (mk_var (loc, Nameops.add_prefix "Build_" spec.spec_name),
                   List.rev_map (spec_field_param_var loc)
                                (all_axioms @ spec.spec_ops))])))
  in

  (* Build the GeneralSpec spec__GSpec for spec *)

  (* FIXME HERE NOW: finish the GeneralSpec *)
  ()

(* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  let spec_id = located_elem spec_lid in
  let _ = begin_module spec_lid in
  let _ = begin_section spec_id in
  let self_globref = Lib.current_mp () in
  declare_spec self_globref spec_id

(* Finish the interactive definition of a spec by completing it *)
let end_new_spec spec_lid =
  let loc = located_loc spec_lid in
  let spec_id = located_elem spec_lid in
  let spec = get_current_spec loc in
  let _ = if not (Id.equal spec.spec_name spec_id) then
            raise loc WrongCurrentSpecName in
  let _ = end_section () in
  let _ = complete_spec loc spec in
  let _ = end_module spec_lid in
  spec


(***
 *** Additions to the Coq parser
 ***)

(* Syntactic class to parse name translation elements *)
VERNAC ARGUMENT EXTEND name_translation_elem
  | [ ident(lhs) "+->" ident(rhs) ] -> [ XlateSingle (lhs,rhs) ]
  | [ ident(lhs) "%" "+->" ident(rhs) "%" ] ->
     [ XlatePrefix (Id.to_string lhs, Id.to_string rhs) ]
END

(* Syntactic class to parse name translations *)
VERNAC ARGUMENT EXTEND name_translation
  | [ name_translation_elem(elem) ";" name_translation (rest) ] -> [ elem::rest ]
  | [ name_translation_elem(elem) ] -> [ [elem] ]
END

(* Syntactic class to parse interp  elements *)
VERNAC ARGUMENT EXTEND interp_map_elem
  | [ ident(lhs) "%" "+->" global(rhs_ref) "%" ] ->
     [ match rhs_ref with
       | Ident (loc, rhs) ->
          InterpMapXlate (loc, XlatePrefix (Id.to_string lhs, Id.to_string rhs))
       | Qualid (loc, q) ->
          user_err_loc (loc, "_", str "Identifier expected") ]
  | [ ident(lhs) "+->" constr(rhs) ] -> [ InterpMapTerm (lhs, rhs) ]
END

(* Syntactic class to parse interp maps *)
VERNAC ARGUMENT EXTEND interp_map
  | [ interp_map_elem(elem) ";" interp_map(rest) ] -> [ elem::rest ]
  | [ interp_map_elem(elem) ] -> [ [elem] ]
END

(* Syntactic class to parse spec terms *)
VERNAC ARGUMENT EXTEND spec_term
  | [ global(r) ] -> [ SpecRef r ]
  | [ spec_term(st) "{" name_translation(xlate) "}" ] -> [ SpecXlate (st, xlate) ]
  | [ spec_term(st) "[" global(interp_ref) "]" ] ->
     [ SpecSubst (st, mkRefC interp_ref) ]
  | [ spec_term(st) "[" global(interp_ref) "{" name_translation(xlate) "}" "]" ] ->
     [ SpecSubstXlate (st, mkRefC interp_ref, xlate) ]
END


(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec

  (* Start an interactive spec definition *)
  | [ "Spec" var(lspec_name) ]
    => [ (Vernacexpr.VtSideff [located_elem lspec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> begin_new_spec lspec_name) ]

  (* End an interactive spec definition *)
  | [ "Spec" "End" var(lspec_name) ]
    => [ (Vernacexpr.VtSideff [located_elem lspec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> ignore (end_new_spec lspec_name)) ]

  (* Start a non-interactive spec definition *)
  | [ "Spec" var(lspec_name) ":=" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [located_elem lspec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let _ = begin_new_spec lspec_name in
            let _ = import_spec_term dummy_loc st in
            ignore (end_new_spec lspec_name)) ]

  (* Start a definition of a spec via refinement *)
(*
  | [ "Spec" var(lspec_name) ":=" "transform" spec_term(st) ]
    => [ (Vernacexpr.VtStartProof ("Classic",Doesn'tGuaranteeOpacity,
                                   [located_elem lspec_name]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let st_expr = refinement_expr_of_spec_term st in
            let spec_id = located_elem lspec_name in
            let refinement_id = add_suffix spec_id "refinement" in
            let loc = located_loc lspec_name in
            let env = Global.env () in
            let evd = Evd.from_env env in
            let pf_expr = mkAppC (mk_specware_ref "RefinementOf",
                                  [mkAppC (mk_specware_ref "ref_spec",
                                           [mk_hole loc; st_expr])]) in
            let (pf_constr,uctx) = Constrintern.interp_constr env evd pf_expr in
            Proof_global.start_proof
              evd refinement_id
              (Global, false, DefinitionBody Definition) [env, pf_constr]
              (fun ending ->
               (* First check that the ending was "Defined" *)
               let _ =
                 match ending with
                 | Proof_global.Proved (false, _, _) -> ()
                 | _ -> user_err_loc
                          (loc, "_",
                           str "Refinements must end with \"Defined\"")
               in
               (* Call the standard proof terminator to save the proof *)
               let _ = Lemmas.standard_proof_terminator
                         [] (Lemmas.mk_hook (fun _ _ -> ())) ending in
               (* FIXME: Why do we need to discard the current proof here? *)
               let _ = Proof_global.discard_current () in
               (* Now create the new spec and import the generated refinement *)
               let _ = begin_new_spec lspec_name in
               let _ = import_refinement_constr_expr
                         loc (mkAppC (mk_specware_ref "refinement_compose",
                                      [st_expr; mk_var (loc, refinement_id)])) in
               end_new_spec lspec_name)) ]
 *)

  (* Add a declared op *)
  | [ "Spec" "Variable" var(lid) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field false lid tp) ]

  (* Add a declared op with a subtype predicate *)
  | [ "Spec" "Variable" var(lid) ":" constr(tp) "|" constr(pred) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let (loc, id) = lid in
            add_spec_field false lid tp;
            add_spec_field false (loc, field_proof_id id) pred) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" var(lid) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let (loc, id) = lid in
            add_spec_field false (loc, field_var_id id) tp;
            add_spec_field false (loc, field_proof_id id)
                           (mk_equality
                              loc
                              (mk_var (loc, field_var_id id))
                              body)) ]

  (* Add a defined op without a type *)
  (* FIXME: figure out how to handle defs with no type... *)
(*
  | [ "Spec" "Definition" ident(id) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) None body) ]
 *)

  (* Add an axiom *)
  | [ "Spec" "Axiom" var(lid) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field true lid tp) ]

  (* Add a theorem *)
  (*
  | [ "Spec" "Theorem" var(lid) ":" constr(tp) ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity,
                                   [located_elem lid]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let loc = located_loc lid in
            let cur_spec = get_current_spec loc in
            let ax_params = List.map
                              (fun (ax_id, _) ->
                               (mk_implicit_assum
                                  (field_param_id ax_id)
                                  (mk_var (loc, field_class_id ax_id))))
                               cur_spec.spec_axioms in
            start_theorem Theorem lid ax_params tp) ]
   *)

  (* Import a spec using a "raw" expression of type RefinementOf *)
  (*
  | [ "Spec" "RawImport" constr(tm) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            import_refinement_constr_expr (constr_loc tm) tm) ]
   *)

  (* Import a spec term *)
  (* FIXME: get the location right *)
  (*
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term dummy_loc st) ]
   *)

  | [ "Spec" "Import" global(r) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions (fun () -> add_spec_import r) ]


  (* Define an interpretation *)
  (*
  | [ "Spec" "Interpretation" var(lmorph_name)
             ":" global(dom) "->" global(codom) ":="
             "{" interp_map(imap) "}"]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity,
                                   [located_elem lmorph_name]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> start_interpretation lmorph_name dom codom (Some imap)) ]
   *)

  (* Define an interpretation using tactics *)
  (*
  | [ "Spec" "Interpretation" var(lmorph_name) ":" global(dom) "->" global(codom) ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity,
                                   [located_elem lmorph_name]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> start_interpretation lmorph_name dom codom None) ]
   *)

END


(* Tactic to do "intro s" where s is computed as a constr *)
(* FIXME: this doesn't work yet... *)
TACTIC EXTEND intro_string_tac
  | [ "intro_string" constr(s) ]
    -> [ let str = destruct_constr string_descr s in
         Tacinterp.eval_tactic 
           (Tacexpr.TacAtom
              (dummy_loc,
               Tacexpr.TacIntroMove (Some (Id.of_string str), MoveLast)))
       ]
END

(* Call a tactic expression, which must evaluate to a tactic function, passing
it an tactic value *)
let tac_call tac_f tac_arg =
  (* First, build the tactic expr (f x) for free variables f and x *)
  let tac_expr =
    Tacexpr.TacArg
      (dummy_loc,
       Tacexpr.TacCall
         (dummy_loc, ArgVar (dummy_loc, Id.of_string "f"),
          [Tacexpr.Reference (ArgVar (dummy_loc, Id.of_string "x"))]))
  in

  (* Next, evaluate tac_f to a tactic value *)
  (Tacinterp.val_interp
     (Tacinterp.default_ist ())
     tac_f
     (fun f_val ->
      (* Now build the tactic environment [f |-> f_val, x |-> tac_arg] *)
      let ist =
        {Tacinterp.default_ist () with
          Tacinterp.lfun =
            Id.Map.add
              (Id.of_string "f") f_val
              (Id.Map.add (Id.of_string "x") tac_arg Id.Map.empty)}
      in

      (* Now, finally, eval tac_expr with tactic environment ist *)
      Tacinterp.eval_tactic_ist ist tac_expr))


(* Tactic to make an evar given a string name and then pass the resulting evar
as a constr to tactic k (which is essentially a continuation). *)
TACTIC EXTEND raw_evar_tac
  | [ "raw_evar" constr(nm) constr(tp) tactic(k) ]
    -> [ Proofview.Goal.enter
           (fun gl_nonnorm ->
            reporting_exceptions
              (fun () ->
               (* Get the current proof state *)
               let gl = Proofview.Goal.assume gl_nonnorm in
               let env = Proofview.Goal.env gl in
               let evdref = ref (Proofview.Goal.sigma gl) in

               (* Normalize nm and destruct it to get a string name *)
               let evar_str = destruct_constr
                                string_descr
                                (hnf_constr ~env_opt:(Some env)
                                            ~evdref_opt:(Some evdref) nm) in

               (* Build the new evar_map with the requested evar *)
               let rec make_evar opt_n =
                 let (evar_id, next_n) =
                   match opt_n with
                   | None -> (Id.of_string evar_str, 0)
                   | Some n ->
                      (Id.of_string (evar_str ^ string_of_int n), n+1)
                 in
                 try
                   let _ = Evd.evar_key evar_id !evdref in
                   make_evar (Some next_n)
                 with Not_found ->
                   Evarutil.new_evar env !evdref
                                     ~src:(Loc.ghost,Evar_kinds.GoalEvar)
                                     ~naming:(IntroIdentifier evar_id)
                                     tp
               in
               let (evd',evar_constr) = make_evar None in

               (* Now we do all the monadic actions *)
               Proofview.tclTHEN
                 (* First set the new evar_map evd' to install the new evar *)
                 (Proofview.Unsafe.tclEVARS evd')
                 (* Now call k, passing in evar_constr *)
                 (tac_call k (Tacinterp.Value.of_constr evar_constr))
       ))]
END


(* Tactic function get extra information for an evar and pass that info to
tactic k, the continuation *)
let get_evar_property evar_constr field_name field descr k =
  Proofview.Goal.enter
    (fun gl_nonnorm ->
     reporting_exceptions
       (fun () ->
        (* Get the current proof state *)
        let gl = Proofview.Goal.assume gl_nonnorm in
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in

        (* Get the evar we care about *)
        let evar =
          match Term.kind_of_term evar_constr with
          | Term.Evar (evar, _) -> evar
          | _ -> user_err_loc (dummy_loc, "_",
                               str ("Not an evar: ")
                               ++ Printer.pr_constr evar_constr)
        in

        (* Extract the field value from the evar *)
        let v =
          match Evd.Store.get (Evd.find evd evar).Evd.evar_extra field with
          | Some v -> v
          | None ->
             user_err_loc (dummy_loc, "_",
                           str "Evar "
                           ++ Printer.pr_constr evar_constr
                           ++ str (" does not have property " ^ field_name))
        in

        (* Now build a constr_expr for v, and interp it to a constr *)
        let v_expr = build_constr_expr descr v in
        let (v_constr,uctx) = Constrintern.interp_constr env evd v_expr in

        (* Now we do all the monadic actions *)
        Proofview.tclTHEN
          (* First merge in any universe constraints from interpreting v_expr *)
          (Proofview.Unsafe.tclEVARS (Evd.merge_universe_context evd uctx))
          (* Now call k, passing in v_constr *)
          (tac_call k (Tacinterp.Value.of_constr v_constr))))

(* Tactic function to tag an evar with extra information from a constr *)
let set_evar_property evar_constr field descr v_constr =
  Proofview.Goal.enter
    (fun gl_nonnorm ->
     reporting_exceptions
       (fun () ->
        (* Get the current proof state *)
        let gl = Proofview.Goal.assume gl_nonnorm in
        let env = Proofview.Goal.env gl in
        let evd = Proofview.Goal.sigma gl in
        let evdref = ref evd in

        (* Get the evar we care about *)
        let evar =
          match Term.kind_of_term evar_constr with
          | Term.Evar (evar, _) -> evar
          | _ -> user_err_loc (dummy_loc, "_",
                               str "Not an evar: "
                               ++ Printer.pr_constr evar_constr)
        in

        (* Extract the value *)
        let v =
          destruct_constr descr (hnf_constr ~env_opt:(Some env)
                                            ~evdref_opt:(Some evdref)
                                            v_constr) in

        (* Now update the evar's store in evd *)
        let evd' = Evd.raw_map
                     (fun evar' info ->
                      if Evar.equal evar evar' then
                        { info with
                          Evd.evar_extra =
                            Evd.Store.set info.Evd.evar_extra field v }
                      else info)
                     !evdref in

        (* Finally, install the new updated evar map *)
        (Proofview.Unsafe.tclEVARS evd')
    ))

(* FIXME: generalize evar properties *)

(* Fields for setting with set_evar_property *)
let evar_property_sort_hint : int Evd.Store.field = Evd.Store.field ()
let evar_property_spec_axiom_p : bool Evd.Store.field = Evd.Store.field ()

TACTIC EXTEND evar_property_sort_hint
  | [ "set_evar_property" "sort_hint" constr(evar) constr(i) ]
    -> [ set_evar_property evar evar_property_sort_hint nat_descr i ]
  | [ "get_evar_property" "sort_hint" constr(evar) tactic(k) ]
    -> [ get_evar_property evar "sort_hint" evar_property_sort_hint nat_descr k ]
END
TACTIC EXTEND evar_property_axiom_p
  | [ "set_evar_property" "spec_axiom_p" constr(evar) constr(b) ]
    -> [ set_evar_property evar evar_property_spec_axiom_p bool_descr b ]
  | [ "get_evar_property" "spec_axiom_p" constr(evar) tactic(k) ]
    -> [ get_evar_property evar "spec_axiom_p" evar_property_spec_axiom_p bool_descr k ]
END


(* Helper type for instantiate_spec *)
type field_evar = {field_evar_evar : Evar.t;
                   field_evar_info : Evd.evar_info;
                   field_evar_tp : Constr.t;
                   field_evar_id : Id.t;
                   field_evar_is_prop : bool}

(* Instantiate a Spec evar using all evars that depend on it as fields *)
TACTIC EXTEND instantiate_spec_tac
  | [ "instantiate_spec" constr(evar_constr) ]
    -> [ Proofview.Goal.nf_enter
           (fun gl ->
            let env = Proofview.Goal.env gl in
            let evd = Proofview.Goal.sigma gl in
            let evd, nf = Evarutil.nf_evars_and_universes evd in

            (* Extract the evar we care about from evar_constr *)
            let spec_evar =
              match Term.kind_of_term evar_constr with
              | Term.Evar (evar, [| |]) -> evar
              | Term.Evar (evar, args) ->
                 user_err_loc (dummy_loc, "_",
                               str "Evar must have empty context")
              | _ -> user_err_loc (dummy_loc, "_",
                                   str "Not an evar: "
                                   ++ Printer.pr_constr evar_constr)
            in
            let spec_id = Evd.evar_ident spec_evar evd in
            let spec_info = Evd.find evd spec_evar in

            (* Check that evar has an empty context *)
            let _ =
              match Evd.evar_context spec_info with
              | [] -> ()
              | _ -> user_err_loc
                       (dummy_loc, "_",
                        str "instantiate_record_type: evar has non-empty context: "
                        ++ Printer.pr_constr (Term.mkEvar (spec_evar, [| |])))
            in

            (* Find all the evars with context of the following form:
               (R:Type) (mod: R -> spec_model ?spec_evar) (r:R) *)
            let (field_evars_type, field_evars_prop) =
              Evd.fold_undefined
                (fun evar info (l_type, l_prop) ->
                 match Evd.evar_context info with
                 | [_, None, hyp_tp1; _, None, hyp_tp2; _, None, hyp_tp3]
                   (* FIXME: check that the evar is ok! *)
                    when
                      not (Evar.Set.mem
                             spec_evar (Evd.evars_of_term
                                          (Evd.evar_concl info)))
                      (*
                      (match Term.kind_of_term hyp_tp with
                       | Term.App (hd, [| arg |]) ->
                          constr_is_inductive
                            (mk_inductive specware_mod "GeneralModelOf") hd
                          && Term.isEvar arg
                          && Evar.equal (fst (Term.destEvar arg)) spec_evar
                          && 
                       | _ -> false) *)
                   ->
                    let field_evar =
                      {field_evar_evar = evar;
                       field_evar_info = info;
                       field_evar_tp = nf (Evd.evar_concl info);
                       field_evar_id = Evd.evar_ident evar evd;
                       field_evar_is_prop =
                         match Retyping.get_sort_family_of
                                 env evd (nf (Evd.evar_concl info)) with
                         | Sorts.InProp -> true
                         | _ -> false }
                    in
                    if field_evar.field_evar_is_prop then
                      (l_type, field_evar::l_prop)
                    else
                      (field_evar::l_type, l_prop)
                 | _ -> (l_type, l_prop))
                evd ([], [])
            in
            let field_evars = field_evars_type @ field_evars_prop in

            (* Sort the evars based on type dependencies *)
            let field_evars_sorted =
              evar_topo_sort
                ~eager:true
                (fun fev -> fev.field_evar_evar)
                (List.fold_left
                   (fun deps fev ->
                    Evar.Map.add
                      fev.field_evar_evar
                      (Evd.evars_of_term fev.field_evar_tp) deps)
                   Evar.Map.empty field_evars)
                field_evars
            in

            (* Split the sorted evars into predicative vs propositional *)
            let (field_evars_type, field_evars_prop) =
              split_list_suffix_pred (fun fe -> fe.field_evar_is_prop)
                                     field_evars_sorted
            in

            (* Helper to replace evars with local variables, in the types of
               evars when building the Spec object *)
            (* FIXME: looks like the default lifting here needs to be 1...? *)
            let rec replace_evars_with_rels evars lifting constr =
              match Term.kind_of_term constr with
              | Term.Evar (ev,args) ->
                 (try
                     let evar_num = index_of (Evar.equal ev) evars in
                     let _ = if Array.length args != 3 then
                               raise dummy_loc
                                     (Failure "instantiate_record_type") in
                     let _ = Pp.msg_info (str "Replacing evar "
                                          ++ Printer.pr_constr constr
                                          ++ str (" with variable number "
                                                  ^ string_of_int (lifting + evar_num)))
                     in
                     Term.mkRel (lifting + evar_num)
                   with Not_found -> constr)
              | _ ->
                 Term.map_constr_with_binders (fun x -> x+1)
                                              (replace_evars_with_rels evars)
                                              lifting constr
            in

            (* Build the required Spec object *)
            let build_axioms evars =
              List.fold_right
                (fun fev rest ->
                 Term.mkApp
                   (Term.mkConstruct (mk_constructor datatypes_mod "cons"),
                    [| Term.mkInd (mk_inductive specware_mod "SpecAxiom");
                       Term.mkApp
                         (Term.mkConstruct
                            (mk_constructor specware_mod "specAxiom"),
                          [| mk_string_constr
                               (Id.to_string fev.field_evar_id);
                             replace_evars_with_rels
                               evars 1 fev.field_evar_tp |]);
                       rest |]))
                field_evars_prop
                (Term.mkApp
                   (Term.mkConstruct (mk_constructor datatypes_mod "nil"),
                    [| Term.mkInd (mk_inductive specware_mod "SpecAxiom") |]))
            in
            let rec build_spec evars fevs =
              match fevs with
              | [] -> Term.mkApp
                        (Term.mkConstruct
                           (mk_constructor specware_mod "Spec_Axioms"),
                         [| build_axioms evars |])
              | fev::fevs' ->
                 let tp = replace_evars_with_rels evars 1 fev.field_evar_tp in
                 Term.mkApp
                   (Term.mkConstruct (mk_constructor specware_mod "Spec_Cons"),
                    [| mk_string_constr (Id.to_string fev.field_evar_id);
                       tp;
                       Term.mkLambda
                         (Name fev.field_evar_id, tp,
                          (* NOTE: we push the evar to the front of evars
                          because rel_contexts are stored inside-out *)
                          build_spec (fev.field_evar_evar::evars) fevs') |])
            in
            let spec_constr = build_spec [] field_evars_type in

            (* Instantiate spec_evar *)
            (* FIXME: instantiate the remaining evars *)
            Proofview.tclTHEN
              (Evar_tactics.instantiate_tac_by_name
                 spec_id
                 (Tacinterp.default_ist (),
                  Detyping.detype true [] env evd spec_constr))
              (Proofview.V82.nf_evar_goals)

            (* let _ = Pp.msg_info (str "Constr: " ++ Printer.pr_constr spec_constr) in
            Proofview.tclUNIT () *)
       )]
END


(* Define a record type for an evar *)
(* FIXME: document this! *)
let add_record_type_for_evar env evd rectp_evar =
  (* Get the necessary info for rectp_evar *)
  let rectp_info = Evd.find evd rectp_evar in
  let rectp_id = Evd.evar_ident rectp_evar evd in

  (* Check that rectp_evar has an empty context *)
  let _ =
    match Evd.evar_context rectp_info with
    | [] -> ()
    | _ -> user_err_loc
             (dummy_loc, "_",
              str "instantiate_record_type: evar has non-empty context: "
              ++ Printer.pr_constr (Term.mkEvar (rectp_evar, [| |])))
  in

  (* Find all the evars with a single hypothesis of type rectp_evar that do not
  contain rectp_evar in the conclusion type *)
  (* FIXME HERE: split into propositional and non-propositional, and add the
  propositional ones last; also need to change the topo sort so it eagerly
  removes all dependencies of the head node, instead of lazily waiting until the
  head node can be removed, so that ops don't get moved past all axioms before
  the one axiom it depends on... Maybe do a lazy reverse sort? *)
  let field_evars : (Evar.t * Evd.evar_info * Id.t * Id.t) list =
    Evd.fold_undefined
      (fun evar info l ->
       match Evd.evar_context info with
       | [hyp_id, None, hyp_tp] ->
          (match Term.kind_of_term hyp_tp with
           | Term.Evar (ev,_) ->
              if Evar.equal ev rectp_evar &&
                   not (Evar.Set.mem
                          rectp_evar (Evd.evars_of_term
                                        (Evd.evar_concl info)))
              then
                (evar, info, Evd.evar_ident evar evd, hyp_id)::l
              else l
           | _ -> l)
       | _ -> l)
      evd []
  in

  (* Sort field_evars, making sure all of the evars occurring in another evar's
  type come before it *)
  let field_evars_sorted =
    evar_topo_sort
      (fun (evar,_,_,_) -> evar)
      (List.fold_left
         (fun deps (evar,info,_,_) ->
          Evar.Map.add
            evar
            (Evd.evars_of_term (Evd.evar_concl info)) deps)
         Evar.Map.empty field_evars)
      field_evars
  in

  (* Helper to replace evars with local variables, in the types of
               evars when building the record type *)
  let rec replace_evars_with_rels evars lifting constr =
    match Term.kind_of_term constr with
    | Term.Evar (ev,args) ->
       (try
           let evar_num = index_of (Evar.equal ev) evars in
           let _ = if Array.length args != 1 then
                     raise dummy_loc
                           (Failure "instantiate_record_type") in
           Term.mkRel (lifting + evar_num)
         with Not_found -> constr)
    | _ ->
       Term.map_constr_with_binders (fun x -> x+1)
                                    (replace_evars_with_rels evars)
                                    lifting constr
  in

  (* Build the field list for the new record type; we use fold_left
               here to reverse the list, since rel_contexts are backwards *)
  let (rectp_fields,_) =
    List.fold_left
      (fun (fields,evars) (evar,info,id,_) ->
       ((Name id, None, replace_evars_with_rels
                          evars 0 (Evd.evar_concl info)) ::fields,
        evar::evars))
      ([],[]) field_evars_sorted in

  (* Create a universe variable for the new record type, requiring it to be
  greater than or equal to the universes of all the fields and less than or
  equal to the universe of rectp_evar *)
  (*
  let rectp_univ_lb =
    List.fold_left (fun univ (_,_,field_tp) ->
                    let s = Retyping.get_sort_of env evd field_tp in
                    Univ.sup (Term.univ_of_sort s) univ)
                   Univ.type0_univ rectp_fields in

  let (evd, rectp_univ) =
    Evd.new_univ_variable Evd.univ_flexible_alg evd in
  let rectp_sort = Term.sort_of_univ rectp_univ in
  let evd = Evd.set_leq_sort env evd
                             (Term.sort_of_univ rectp_univ_lb)
                             rectp_sort in
  (*
  let evd =
    Evd.set_leq_sort
      env evd rectp_sort
      (Term.destSort
         (Evd.existential_type evd (rectp_evar, [| |]))) in *)

  (*
  let rectp_sort =
    Term.destSort (Evd.existential_type evd (rectp_evar, [| |])) in
  let evd = Evd.set_leq_sort env evd
                             (Term.sort_of_univ rectp_univ_lb)
                             rectp_sort in *)

  let evd, nf = Evarutil.nf_evars_and_universes evd in
  let rectp_type = nf (Term.mkSort rectp_sort) in
  let rectp_fields =
    List.map (fun (nm, d, tp) -> (nm, d, nf tp)) rectp_fields in
   *)


  (* Create the record type *)
  let rectp_ind =
    (*
    add_record_type_constr evd rectp_id rectp_type [] rectp_fields
     *)
    (*
    match Record.definition_structure
            (Record, false, BiFinite, (false, (dummy_loc, rectp_id)),
             [],
             (List.map
                (fun (nm, _, tp_expr) ->
                 let tp =
                   Constrextern.extern_constr true env evd tp_expr
                 in
                 (((None,
                    (AssumExpr ((dummy_loc, nm), tp))), None), []))
                rectp_fields),
             (Nameops.add_prefix "Build_" rectp_id),
             (Some type_expr)) with
    | IndRef i -> i
    | _ ->
       anomaly (str "Non-inductive returned by Record.definition_structure")
     *)
    let _ =
      interp
        (dummy_loc,
         VernacInductive (false, BiFinite,
                          [((false, (dummy_loc, rectp_id)), [],
                            Some type_expr,
                            Record,
                            RecordDecl
                              (None,
                               List.map
                                 (fun (nm, _, tp) ->
                                  let tp =
                                    Constrextern.extern_constr true env evd tp
                                  in
                                  let id = match nm with Name id -> id in
                                  mk_record_field ((dummy_loc, id), tp, false))
                                 rectp_fields)),
                           []]))
    in
    match Nametab.locate (qualid_of_ident rectp_id) with
    | IndRef ind -> ind
  in

  (* Return the new evd, rectp_ind, and all the field evars *)
  (evd, rectp_ind, field_evars_sorted)


TACTIC EXTEND instantiate_record_type_tac
  | [ "instantiate_record_type" constr(evar_constr) ]
    -> [ Proofview.Goal.enter
           (fun gl_nonnorm ->
            reporting_exceptions
              (fun () ->
               (* Get the current proof state *)
               let gl = Proofview.Goal.assume gl_nonnorm in
               let env = Proofview.Goal.env gl in
               let evd = Proofview.Goal.sigma gl in

               (* Extract the evar we care about from evar_constr *)
               let rectp_evar =
                 match Term.kind_of_term evar_constr with
                 | Term.Evar (evar, [| |]) -> evar
                 | Term.Evar (evar, args) ->
                    user_err_loc (dummy_loc, "_",
                                  str "Evar must have empty context")
                 | _ -> user_err_loc (dummy_loc, "_",
                                      str "Not an evar: "
                                      ++ Printer.pr_constr evar_constr)
               in
               let rectp_id = Evd.evar_ident rectp_evar evd in

               (* Add the record type *)
               let (evd, rectp_ind, field_evars_sorted) =
                 add_record_type_for_evar env evd rectp_evar in

               (* Now we finish with all the monadic actions *)
               (Proofview.tclTHEN
                  (Proofview.Unsafe.tclNEWGOALS [rectp_evar])
                  (Proofview.tclTHEN
                     (Proofview.cycle (-1))
                     (Tactics.tclABSTRACT
                        None
                        (Tactics.Simple.apply (Term.mkInd rectp_ind)))))

               (*
               Proofview.tclTHEN
                 (* Install the new updated evar map *)
                 (Proofview.tclTHEN
                    (Proofview.tclEFFECTS
                       (Declareops.side_effects_of_list []))
                    (Proofview.Unsafe.tclEVARS evd))
                 (* Define rectp_evar to be the new record type, and all the
                 field evars to be the projections *)
                 (List.fold_left
                    (fun m (evar_id, evar_def) ->
                     Proofview.tclTHEN
                       m
                       (Evar_tactics.instantiate_tac_by_name
                          evar_id
                          (Tacinterp.default_ist (), evar_def)))
                    (Proofview.tclUNIT ())
                    ((rectp_id,
                      (Glob_term.GRef (dummy_loc, IndRef rectp_ind, None)))
                     ::(List.map
                          (fun (_, _, id, hyp_id) ->
                           (* FIXME: maybe use Recordops.lookup_projects? *)
                           let proj_const =
                             Nametab.locate_constant (qualid_of_ident id) in
                           (id,
                            Glob_term.GApp
                              (dummy_loc,
                               Glob_term.GRef (dummy_loc,
                                               ConstRef proj_const, None),
                               [Glob_term.GVar (dummy_loc, hyp_id)])))
                          field_evars_sorted))) *)
       ))]
END


(* Set a debug terminator *)
VERNAC COMMAND EXTEND Debug_terminator
  | [ "Debug" "Terminator" ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ Proof_global.set_terminator
           (fun _ ->
            ()
              (* raise dummy_loc (Failure "Debug Terminator") *)) ]
END


(* A debug-mode version of Defined *)
VERNAC COMMAND EXTEND Defined_debug
  | [ "Defined_Debug" ]
    => [ (Vernacexpr.VtQed Vernacexpr.VtKeep, Vernacexpr.VtLater) ]
    -> [ (* let proof =
           Proof_global.close_proof ~keep_body_ucst_sepatate:false (fun x -> x)
         in *)
         (* Lemmas.save_proof (* ~proof *) (Proved (true, None)) *)
    interp (dummy_loc, VernacEndProof (Proved (true, None)))
 ]
END


(* Print all the modules that are registered as spec *)
VERNAC COMMAND EXTEND Print_registered_spec
  | [ "Print_Specs" ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ Pp.msg_info
           (Pp.prlist_with_sep
              (fun _ -> str " ")
              (fun (globref,_) ->
               str (Names.ModPath.to_string globref))
              (MPmap.bindings !spec_table)) ]
END
