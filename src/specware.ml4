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

(* The axiom typeclass field pointing to an instance of this axiom *)
let field_axelem_id f = add_suffix f "axiom"

(* The name of the Spec representation of a spec named s_id *)
let spec_repr_id s_id = add_suffix s_id "Spec"

(* The name of the parameteric model constructor for a spec named s_id *)
let spec_model_id s_id = add_suffix s_id "model"

(* The name of the IsoToSpec proof for a spec named s_id *)
let spec_iso_id s_id = add_suffix s_id "Iso"

(* Get the Id for the interpretation for import number i *)
let spec_import_id i =
  add_suffix (Id.of_string "spec") ("import" ^ string_of_int i)

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

(* The type of predicates on ops (see Spec.v), where 'a is the underlying term
type being used, either Constr.t or constr_expr *)
type 'a oppred =
  | Pred_Trivial
  | Pred_Eq of 'a
  | Pred_Fun of 'a

let map_oppred f oppred =
  match oppred with
  | Pred_Trivial -> Pred_Trivial
  | Pred_Eq x -> Pred_Eq (f x)
  | Pred_Fun x -> Pred_Fun (f x)

let oppred_is_nontrivial oppred =
  match oppred with
  | Pred_Trivial -> false
  | _ -> true

let oppred_is_eq oppred =
  match oppred with
  | Pred_Eq _ -> true
  | _ -> false

(* The type of ops, using underlying term type 'a *)
type 'a op = (Id.t * 'a * 'a oppred)

let map_op (f : 'a -> 'b) (op: 'a op) : 'b op =
  let (op_id,op_tp,oppred) = op in
  (op_id, f op_tp, map_oppred f oppred)

let op_params (op: constr_expr op) : (Id.t * constr_expr) list =
  let (op_id,op_tp,oppred) = op in
  match oppred with
  | Pred_Trivial ->
    [field_param_id op_id, op_tp]
  | Pred_Eq t ->
    [field_param_id op_id, op_tp;
     field_proof_param_id op_id,
     mk_equality (mk_var (dummy_loc, field_param_id op_id)) t]
  | Pred_Fun pred ->
    [field_param_id op_id, op_tp;
     field_proof_param_id op_id, pred]

let op_param_ids (op : 'a op) : Id.t list =
  let (op_id,_,oppred) = op in
  if oppred_is_nontrivial oppred then
    [field_param_id op_id; field_proof_param_id op_id]
  else
    [field_param_id op_id]

(* FIXME: documentation *)
(* NOTE: the op constrs are all in the context of the ops (and their proofs) of
the importing spec, while the axiom constrs are in the context of the ops and
the axioms of the importing spec *)
type spec_import = {
  spec_import_globref : spec_globref;
  spec_import_op_constrs : (Constr.t op) list;
  (* spec_import_axiom_constrs : (Id.t * Constr.t) list; *)
  spec_import_interp : Constr.t
}

type spec_import_group = {
  spec_impgrp_num : int;
  spec_impgrp_ops : (Id.t * bool) list;
  spec_impgrp_axioms : Id.t list;
  spec_impgrp_imports : spec_import list
}

(* A spec contains its name, its module path, and its op and axiom names. Note
that ops and axioms --- collectively called the "fields" of the spec --- are
stored in reverse order, for efficiency of adding new ones. *)
type spec = {
  spec_name : Id.t;
  spec_path : DirPath.t;
  spec_ops : (constr_expr op) list;
  spec_axioms : (Id.t * constr_expr) list;
  spec_imports : spec_import_group list
}

(* Get the type-class accessor name for an op *)
let op_accessor_id (op : 'a op) : Id.t =
  let (id, _, oppred) = op in
  if oppred_is_eq oppred then
    field_var_id id
  else id

(* Build a constr_expr for the predicate corresponding to an op. The in_spec
flag says whether we should assume the associated f__class and f__pred
type-classes have already been defined. *)
let op_pred_expr ?(in_spec=false) loc (op : constr_expr op) : constr_expr =
  let (id, _, oppred) = op in
  match oppred with
  | Pred_Trivial ->
     mk_reference ["Coq"; "Init"; "Logic"] "True"
  | Pred_Eq eq_expr ->
     mk_equality (mk_var (loc, if in_spec then field_var_id id
                               else field_param_id id)) eq_expr
  | Pred_Fun pred_expr ->
     pred_expr

(* Build the expression binder (f1__param:T) (f1__proof__param:P), body where
"binder" is "forall" when as_type is true and "lambda" when as_type is false.
When op is a defined op, also add a let-expression f1 := f1_def around body.
NOTE: T and P here do not use the op type-classes, i.e., we are assuming we are
not "in the spec". *)
let abstract_op loc as_type (op: constr_expr op) body : constr_expr =
  let (op_id,op_tp,oppred) = op in
  let full_body =
    match oppred with
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

(* Create an empty spec with the given name *)
let make_empty_spec spec_id =
  { spec_name = spec_id; spec_path = Lib.cwd_except_section ();
    spec_ops = []; spec_axioms = []; spec_imports = [] }

(* Whether spec contains an op or axiom named f *)
let contains_field spec f =
  List.exists (fun (f',_,_) -> Id.equal f f') spec.spec_ops ||
    List.exists (fun (f', _) -> Id.equal f f') spec.spec_axioms

(* Check that a field (op or axiom) of the given name exists in the current spec *)
let spec_field_exists f =
  let res = Nametab.exists_cci (Lib.make_path f) in
  let _ = debug_printf 2 "@[spec_field_exists (%s): %B@]\n" (Id.to_string f) res in
  res

(* Find an unused import number in spec *)
let find_unused_import_id spec =
  let slots = Array.make (List.length spec.spec_imports) false in
  let _ = List.iter (fun imp -> slots.(imp.spec_impgrp_num) <- true)
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
    spec_ops = List.filter (fun op ->
                            spec_field_exists (op_accessor_id op)) spec.spec_ops;
    spec_axioms = List.filter (fun (id,_) -> spec_field_exists id) spec.spec_axioms;
    spec_imports =
      List.filter (fun impgrp ->
                   spec_field_exists (spec_import_id impgrp.spec_impgrp_num))
                  spec.spec_imports }

(* Find all the __param and __proof_param implicit arguments on which a
locally-defined identifier id depends *)
let field_param_deps id =
  let gr = Nametab.locate (qualid_of_ident id) in
  (* FIXME: this just checks if an implicit argument name is f__param or
  f__proof__param for some existing field f; maybe this should be more
  subtle...? *)
  List.filter
    (fun id ->
     match match_param_id id, match_proof_param_id id with
     | Some f, None
     | _, Some f ->
        (try Nametab.exists_cci
               (Nametab.full_name_cci (qualid_of_ident f))
         with Not_found -> false)
     | _,_ -> false)
    (implicit_arg_ids gr)


(***
 *** Exceptions
 ***)

(* There is no current spec *)
exception NoCurrentSpec

(* There is already a current spec *)
exception CurrentSpecExists

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Field already exists in the current spec *)
exception FieldExists of Id.t

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

(* Map over all registered specs, removing any that are "stale", i.e., that are
no longer valid (because of Undos) *)
let registered_spec_map f =
  MPmap.fold (fun globref spec l ->
              try
                if Nametab.exists_dir (Nametab.dirpath_of_module globref) then
                  f (globref, spec)::l
                else
                  raise dummy_loc Not_found
              with Not_found ->
                let _ = spec_table := MPmap.remove globref !spec_table in
                l) !spec_table []


(***
 *** Inductive Descriptions of Specs and Refinements
 ***)

(* A description of strings that parses into Id.t *)
let id_descr : (Id.t, Id.t) constr_descr =
  hnf_descr (Descr_Iso ("id", Id.of_string, Id.to_string, string_fast_descr))

(* A description of an OpPred. Note that the constr_expr side is a pair, of the
oppred itself as well as the type of the underlying op, which is needed to build
a constr_expr for the oppred. *)

let oppred_descr f : (Constr.t oppred,
                      constr_expr * constr_expr oppred) constr_descr =
  Descr_Iso
    ("OpPred",
     (function
       | Left (_, ()) -> Pred_Trivial
       | Right (Left (_, (x, ()))) -> Pred_Eq x
       | Right (Right (Left (_, (pred, ())))) ->
          Pred_Fun (Term.mkApp (pred, [| Term.mkVar (field_param_id f) |]))
       | Right (Right (Right emp)) -> emp.elim_empty),
     (function
       | (tp, Pred_Trivial) -> Left (tp, ())
       | (tp, Pred_Eq x) -> Right (Left (tp, (x, ())))
       | (tp, Pred_Fun pred) ->
          Right (Right (Left (tp, (mkCLambdaN
                                     dummy_loc
                                     [mk_explicit_var_assum (field_param_id f)]
                                     pred, ()))))),
     unary_ctor
       specware_mod "Pred_Trivial" Descr_Constr
       (binary_ctor
          specware_mod "Pred_Eq"
          Descr_Constr (fun _ -> Descr_Constr)
          (binary_ctor
             specware_mod "Pred_Fun"
             Descr_Constr (fun _ -> Descr_Constr)
             Descr_Fail)))

(* A description of the SpecAxiom type *)
let spec_axiom_descr : (Id.t * Constr.t, Id.t * constr_expr) constr_descr =
  Descr_Iso
    ("SpecAxiom",
     (function
       | Left (f, (tp, ())) -> (f, tp)
       | Right emp -> emp.elim_empty),
     (fun (f,tp) -> Left (f, (tp, ()))),
     binary_ctor
       specware_mod "specAxiom" id_descr (fun _ -> Descr_Constr) Descr_Fail)

(* The description of a list of axioms *)
let axiom_list_descr : ((Id.t * Constr.t) list,
                        (Id.t * constr_expr) list) constr_descr =
  list_descr spec_axiom_descr

type spec_fields = (constr_expr op) list * (Id.t * constr_expr) list
type spec_fields_constr = (Constr.t op) list * (Id.t * Constr.t) list

(* The description of the Spec inductive type. *)
let spec_descr : (spec_fields_constr, spec_fields) constr_descr =
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
             Left (f, (tp, ((tp, oppred), ((ops', axioms), ()))))
          | ([], axioms) -> Right (Left (axioms, ()))),
        quaternary_ctor
          specware_mod "Spec_Cons"
          (hnf_descr id_descr) (fun _ -> Descr_Constr)
          (fun f_sum _ ->
           let f = match f_sum with Left f -> f | Right f -> f in
           oppred_descr f)
          (fun f_sum tp_sum oppred_sum ->
           let f = match f_sum with Left f -> f | Right f -> f in
           let (is_eq, is_nontrivial) =
             match oppred_sum with
             | Left oppred -> (oppred_is_eq oppred, oppred_is_nontrivial oppred)
             | Right (_, oppred) ->
                (oppred_is_eq oppred, oppred_is_nontrivial oppred)
           in
           Descr_ConstrMap
             ((fun rest_constr ->
               let rest_body_constr =
                 Reduction.beta_appvect
                   rest_constr [| Term.mkVar (field_param_id f);
                                  Term.mkVar (field_proof_param_id f) |] in
               let rest_body_constr' =
                 match Term.kind_of_term rest_body_constr with
                 | Term.LetIn (nm, _, rhs_tp, let_body) when is_eq ->
                    (* NOTE: if the current oppred is an equality, then we expect
                    a let-expression here binding the definition of the op; we
                    then replace the let-bound variable here with free var f *)
                    Reduction.beta_appvect
                      (Term.mkLambda (nm, rhs_tp, let_body)) [| Term.mkVar f |]
                 | _ -> rest_body_constr in
               hnf_constr rest_body_constr'),
              (fun rest_expr ->
               (* Make a lambda expression for the rest argument of Spec_Cons.
               The expressions class_expr and pred_expr are applications of
               f__class and f__pred, respectively, to all of their implicit
               arguments corresponding to fields in the current spec. *)
               let class_expr =
                 mk_id_app_named_args dummy_loc (field_class_id f)
                                      (List.map
                                         (fun id -> (id, mk_var (dummy_loc, id)))
                                         (field_param_deps (field_class_id f)))
               in
               let pred_expr =
                 if is_nontrivial then
                   mk_id_app_named_args
                     dummy_loc (field_pred_id f)
                     (List.map (fun id -> (id, mk_var (dummy_loc, id)))
                               (field_param_deps (field_pred_id f)))
                 else
                   CHole (dummy_loc, None, IntroAnonymous, None)
               in
               (mkCLambdaN
                  dummy_loc
                  [LocalRawAssum ([dummy_loc, Name (field_param_id f)], Default Explicit,
                                  class_expr);
                   LocalRawAssum ([dummy_loc, Name (field_proof_param_id f)],
                                  Default Explicit, pred_expr)]
                  (if is_eq then
                     CLetIn (dummy_loc, (dummy_loc, Name f),
                             mkAppC (mk_specware_ref "def",
                                     [mk_var (dummy_loc, field_param_id f);
                                      mk_var (dummy_loc, field_proof_param_id f)]),
                             rest_expr)
                   else
                     rest_expr))),
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
    build_constr_expr spec_descr (List.rev spec.spec_ops,
                                  List.rev spec.spec_axioms) in
  let _ = debug_printf 1 "@[build_spec_repr (1):@ %a@]\n"
                       pp_constr_expr spec_expr in
  (* Internalize spec_expr into a construction *)
  let (constr,uctx) = Constrintern.interp_constr env evd spec_expr in
  let _ = debug_printf 1 "@[build_spec_repr (2):@ %a@]\n"
                       pp_constr constr in

  (* Helper definitions *)
  let consop_constructor = mk_constructor loc specware_mod "Spec_Cons" in
  let axioms_constructor = mk_constructor loc specware_mod "Spec_Axioms" in
  (* Helper: unfold constants in constr using const_map, which either maps to a
  variable id in scope or to None, meaning the constant should be unfolded *)
  let rec unfold_helper const_map constr =
    let unfold_const_app const args =
      try
        let const_unfolded =
          match Cmap.find (fst const) const_map with
          | Some var_id -> Term.mkVar var_id
          | None ->
             (* NOTE: the value of const could still require unfolding *)
             unfold_helper const_map (Environ.constant_value_in env const)
        in
        Reduction.beta_appvect const_unfolded args
      with Not_found ->
        Constr.map (unfold_helper const_map) constr
    in
    match Term.kind_of_term constr with
    | Term.Const const ->
       unfold_const_app const [| |]
    | Term.App (head, args)
         when Term.isConst head ->
       (match Term.kind_of_term head with
        | Term.Const const ->
           unfold_const_app const (Array.map (unfold_helper const_map) args)
        | _ -> raise loc (Failure "unfold_helper"))
    | _ -> Constr.map (unfold_helper const_map) constr
  in
  (* Helpers to add ids to a const_map *)
  let const_map_add ?(var_opt=None) id const_map =
    let const = Nametab.locate_constant (qualid_of_ident id) in
    Cmap.add const var_opt const_map
  in
  let const_map_add_multi ids const_map =
    List.fold_right const_map_add ids const_map in
  (* Helper: unfold a rest function, the 4th argument of Spec_Cons, depending
  on the form of the oppred *)
  let rec unfold_rest_fun const_map rem_ops' op_id oppred rest_f =
    let (f__proof__param,f__proof__param_tp,f__param,f__param_tp,body) =
      match Term.decompose_lam_n 2 rest_f with
      | ((nm1,tp1)::(nm2,tp2)::[], body) -> (nm1,tp1,nm2,tp2,body)
      | _ -> raise loc (Failure "unfold_rest_fun")
    in
    (* Recursively unfold the body depending on the oppred *)
    let (const_map', body') =
      if oppred_is_eq oppred then
        (* For equality predicates, unfold f__var, f__class, f__proof, and
        f__pred, and replace f itself with the local let-bound variable *)
        let (f__def_nm, rhs, rhs_tp, inner_body) = Term.destLetIn body in
        let f__def = match f__def_nm with
          | Name x -> x
          | _ -> raise loc (Failure "unfold_rest_fun (2)")
        in
        let const_map' =
          const_map_add_multi [field_var_id op_id; field_class_id op_id;
                               field_proof_id op_id; field_pred_id op_id]
                              const_map
        in
        (* NOTE: we don't want to export the unfolding of f to a local let-bound
        variable outside the scope of the let, so we separate const_map'
        (without the local let-bound variable) from const_map'' (with it) *)
        (* let const_map'' = const_map_add ~var_opt:(Some f__def) op_id const_map' in *)
        (* FIXME HERE: cannot just replace the constructor f with the local
        variable f__def, because we need to remove all of f's implicit
        arguments! *)
        let const_map'' = const_map_add op_id const_map' in
        (const_map_add op_id const_map',
         Term.mkLetIn (Name f__def, unfold_helper const_map rhs,
                       unfold_helper const_map rhs_tp,
                       unfold_spec_repr const_map'' rem_ops' inner_body))
      else if oppred_is_nontrivial oppred then
        (* For functional oppreds, unfold f, f__class, f__proof, and f__pred *)
        let const_map' =
          const_map_add_multi [op_id; field_class_id op_id;
                               field_proof_id op_id; field_pred_id op_id]
                              const_map in
        (const_map', unfold_spec_repr const_map' rem_ops' body)
      else
        (* For trivial oppred, just unfold f and f__class *)
        let const_map' =
          const_map_add_multi [op_id; field_class_id op_id] const_map in
        (const_map', unfold_spec_repr const_map' rem_ops' body)
    in
    (* Now re-form the appropriate lambda *)
    Term.mkLambda
      (f__param, unfold_helper const_map' f__param_tp,
       Term.mkLambda
         (f__proof__param, unfold_helper const_map' f__proof__param_tp,
          body'))

  (* Helper: unfold all the constant definitions in a Spec *)
  and unfold_spec_repr const_map rem_ops constr =
    match Term.kind_of_term constr with
    | Term.App (head, args)
         when constr_is_constructor axioms_constructor head ->
       Term.mkApp (head, Array.map (unfold_helper const_map) args)
    | Term.App (head, [| f_c; tp_c; oppred_c; rest_c |])
         when constr_is_constructor consop_constructor head ->
       let ((op_id,_,oppred),rem_ops') =
         match rem_ops with
         | op::rem_ops' -> (op,rem_ops')
         | [] -> raise loc (Failure "unfold_spec_repr")
       in
       let _ =
         if not (Id.equal op_id (destruct_constr id_descr f_c)) then
           raise loc (Failure "unfold_spec_repr")
       in
       Term.mkApp (head,
                   [| unfold_helper const_map f_c;
                      unfold_helper const_map tp_c;
                      (* NOTE: functional oppreds can refer to their op as f
                      instead of f__param... *)
                      unfold_helper (const_map_add op_id const_map) oppred_c;
                      unfold_rest_fun const_map rem_ops' op_id oppred rest_c |])
    | _ -> raise loc (Failure "unfold_spec_repr")
  in

  (* Now, unfold all the f, f__var, f__proof, f_pred, and f__class constants *)
  let constr_unfolded = unfold_spec_repr Cmap.empty (List.rev spec.spec_ops) constr in
  let _ = debug_printf 1 "@[build_spec_repr (3):@ %a@]\n"
                       pp_constr constr_unfolded in
  (constr_unfolded, uctx)


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
               FDeltaBut (registered_spec_map
                            (fun (spec_globref,_) ->
                             AN (global_spec_repr_ref dummy_loc spec_globref)))])]
      constr
  in
  match Term.kind_of_term constr_red with
  | Term.Const (c, _) -> Constant.modpath c
  | Term.Ind (ind, _) -> ind_modpath ind
  | Term.Construct (c, _) -> constr_modpath c
  | _ ->
     user_err_loc (dummy_loc, "_",
                   str "Not a global spec: "
                   ++ Printer.pr_constr constr)

type refinement_import = constr_expr * constr_expr
type refinement_import_constr = {
  ref_import_fromspec: spec_globref;
  ref_import_interp: Constr.t
}

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
       specware_mod "Build_RefinementImport"
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
       specware_mod "Build_RefinementOf"
       (hole_descr Descr_Constr)
       (fun _ -> hnf_descr spec_descr)
       (fun _ _ -> Descr_Constr)
       (fun _ _ _ -> hnf_descr (list_descr (hnf_descr refinement_import_descr)))
       Descr_Fail)

let destruct_refinementof constr =
  try
    destruct_constr refinementof_descr (hnf_constr constr)
  with DescrFailed (tag,sub_constr) ->
    raise dummy_loc (MalformedRefinement (constr,tag,sub_constr))


(***
 *** Inductive Descriptions of Models
 ***)

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


(***
 *** Building Up the Current Spec
 ***)

(* The currrent spec being defined, if one exists *)
let current_spec : spec option ref = ref None

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
let add_spec_field axiom_p lid tp oppred =
  (* Extract the field id and loc from field_name *)
  let f = located_elem lid in
  let loc = located_loc lid in
  let acc_id = op_accessor_id (f,tp,oppred) in

  update_current_spec
    loc
    (fun spec ->
     (* First, check that the given field name does not already exist *)
     let _ = if contains_field spec f then
               raise loc (FieldExists f)
             else ()
     in
     (* Test that we do not have an axiom with a (non-trivial) predicate *)
     let _ =
       match axiom_p, oppred with
       | false, _ -> ()
       | true, Pred_Trivial -> ()
       | true, _ ->
          anomaly ~loc:loc (str "Declaration of an axiom with an op predicate")
     in
     (* Add the operationaly type-class f__class := acc : tp *)
     let _ = add_typeclass (loc, field_class_id f) true axiom_p []
                           [((loc, acc_id), tp, false)]
     in

     if axiom_p then
       (* For axioms, just add the new axiom to the current spec *)
       { spec with spec_axioms = (f,tp)::spec.spec_axioms }

     else
       (* For ops, add an instance of the type-class to the context *)
       let _ =
         add_to_context [mk_implicit_assum
                           (field_param_id f)
                           (mk_var (loc, field_class_id f))] in
       let _ =
         match oppred with
         | Pred_Trivial -> ()
         | _ ->
            (* For ops with predicates, add typeclass
               f__pred : Prop := f__proof : pred *)
            let _ =
              add_typeclass (loc, field_pred_id f) true true []
                            [(loc, field_proof_id f),
                             op_pred_expr loc (f, tp, oppred), false] in
            (* Add f__proof__param : f__pred to the context *)
            let _ =
              add_to_context [mk_implicit_assum
                                (field_proof_param_id f)
                                (mk_var (loc, field_pred_id f))] in
            (* For defined ops, also add a local definition of the form
               f := def f__var f__proof *)
            (match oppred with
             | Pred_Eq _ ->
                add_definition lid [] None
                               (mkAppC
                                  (mk_specware_ref "def",
                                   [mk_var (loc, acc_id);
                                    mk_var (loc, field_proof_id f)]))
             | _ -> ())
       in
       (* Then, finally, add the op to the current spec *)
       { spec with spec_ops = (f,tp,oppred)::spec.spec_ops })


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

(* Inductive description of SpecTranslationElem objects *)
let spec_translation_elem_descr : (spec_translation_elem,
                                   spec_translation_elem) constr_descr =
  Descr_Iso
    ("SpecTranslationElem",
     (function
       | Left (f_from, (f_to, ())) -> XlateSingle (f_from, f_to)
       | Right (Left (f_from_prefix, (f_to_prefix, ()))) ->
          XlatePrefix (f_from_prefix, f_to_prefix)
       | Right (Right emp) -> emp.elim_empty),
     (function
       | XlateSingle (f_from, f_to) -> Left (f_from, (f_to, ()))
       | XlatePrefix (f_from_prefix, f_to_prefix) ->
          Right (Left (f_from_prefix, (f_to_prefix, ())))),
     binary_ctor
       specware_mod "XlateSingle" id_descr (fun _ -> id_descr)
       (binary_ctor
          specware_mod "XlatePrefix"
          string_fast_descr (fun _ -> string_fast_descr)
          Descr_Fail))

(* Inductive description of SpecTranslation objects *)
let spec_translation_descr : (spec_translation, spec_translation) constr_descr =
  Descr_Iso
    ("SpecTranslation",
     (function
       | Left (elems, ()) -> elems
       | Right emp -> emp.elim_empty),
     (fun elems -> Left (elems, ())),
     unary_ctor
       specware_mod "mkSpecTranslation" (list_descr spec_translation_elem_descr)
       Descr_Fail)

(* Translate an id using a single translation_elem, returning None if the
translation_elem had no effect; same as translate_field1 in Spec.v *)
let translate_field1 xlate_elem f =
  match xlate_elem with
  | XlateSingle (f_from, f_to) ->
     if Id.equal f f_from then
       Some f_to
     else None
  | XlatePrefix (from_prefix, to_prefix) ->
     (match match_prefix f from_prefix with
      | None -> None
      | Some f_suf -> Some (Id.of_string (to_prefix ^ f_suf)))

(* Translate an id; this is the same as translate_field in Spec.v *)
let rec translate_field xlate f =
  match xlate with
  | [] -> f
  | elem::xlate' ->
     (match translate_field1 elem f with
      | None -> translate_field xlate' f
      | Some res -> res)


(***
 *** Interpretations
 ***)

(* FIXME HERE NOW: this no longer takes codom_ops! *)
let add_instance_for_interp loc id params dom_globref interp codom_model =
  raise loc (Failure "add_instance_for_interp")
(*
  (* Build a Coq environment with the params *)
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evdref = ref evd in
  let (_, ((env_with_params, _), _)) =
    Constrintern.interp_context_evars env evdref params in

  (* Look up the spec structure for the domain spec *)
  let dom_spec = lookup_global_spec dom_globref in

  (* Normalize the term (map_ops interp codom_ops) to get the ops of the domain
     spec in terms of the ops of the co-domain spec *)
  let (map_ops_constr, uctx) =
    Constrintern.interp_constr
      env_with_params !evdref
      (mkAppC (mk_specware_ref "map_ops", [interp; codom_ops])) in
  let map_ops_constr_red =
    compute_constr
      ~env_opt:(Some env_with_params) ~evdref_opt:(Some evdref)
      map_ops_constr in
  let op_constr_list =
    destruct_constr (spec_ops_descr ~env_opt:(Some env_with_params)
                                    ~evdref_opt:(Some evdref) ())
                    map_ops_constr_red in
  (* Helper to substitute the param variable names for the "rel" variables that
  were introduced in env_with_params *)
  let subst_vars constr =
    Vars.substl
      (List.rev_map (function
                      | (_, Name id) -> Term.mkVar id
                      | (_, Anonymous) ->
                         raise loc (Failure "add_instance_for_interp"))
                    (names_of_local_assums params))
      constr in

  (* Build a list that maps each op in the domain spec to the constrs that build
     it and (optionally) its proof in the co-domain spec *)
  let op_constrs =
    List.map2
      (fun (op_id, _, oppred) (op_constr, op_proof_constr) ->
       (op_id, subst_vars op_constr,
        map_oppred (fun _ -> subst_vars op_proof_constr) oppred))
      (List.rev dom_spec.spec_ops) op_constr_list
  in

  (* Build a list of the arguments of the domain spec's typeclass *)
  (* FIXME: figure out a way to not use extern_constr here (which would need a
  way to add type-class instances from constrs instead of constr_exprs...) *)
  let typeclass_args =
    concat_map (fun (op_id, op_constr, op_pf_oppred) ->
                (field_param_id op_id, Constrextern.extern_constr
                                         true env !evdref op_constr)
                ::(match op_pf_oppred with
                   | Pred_Trivial -> []
                   | Pred_Eq op_pf_constr ->
                      [field_proof_param_id op_id,
                       Constrextern.extern_constr
                         true env !evdref op_pf_constr]
                   | Pred_Fun op_pf_constr ->
                      [field_proof_param_id op_id,
                       Constrextern.extern_constr
                         true env !evdref op_pf_constr]))
               op_constrs in

  (* Now add the actual instance *)
  let _ =
    add_term_instance
      (loc, Name id)
      params
      (mk_ref_app_named_args loc
                             (global_spec_typeclass_ref loc dom_globref)
                             typeclass_args)
      (mkAppC
         (mk_reference ["Coq"; "Init"; "Logic"] "proj2",
          [mk_ref_app_named_args
             loc
             (Qualid (loc, mk_qualid specware_mod "spec_models_iso"))
             [Id.of_string "IsoToSpecModels",
              mk_ref_app_named_args
                loc
                (global_spec_iso_ref loc dom_globref)
                typeclass_args];
           mkAppC
             (mk_specware_ref "map_model", [interp; codom_ops; codom_model])]))
  in

  op_constrs
 *)

(* Mappings from names in a domain spec to names or terms in a codomain spec *)
type interp_map_elem =
  (* Map a name to another name using a spec translation *)
  | InterpMapXlate of Loc.t * spec_translation_elem
  (* Map a name to an expression *)
  | InterpMapTerm of Id.t * constr_expr
type interp_map = interp_map_elem list

(* Apply an interp_map to an identifier *)
let rec apply_interp_map top_loc interp_map f =
  match interp_map with
  | [] -> mk_var (top_loc, f)
  | (InterpMapXlate (xloc, xelem))::interp_map' ->
     (match translate_field1 xelem f with
      | Some f' -> mk_var (xloc, f')
      | None -> apply_interp_map top_loc interp_map' f)
  | (InterpMapTerm (f_from, expr_to))::interp_map' ->
     if Id.equal f f_from then expr_to else
       apply_interp_map top_loc interp_map' f

(* Start an interactive proof of an interpretation named lid from dom to codom,
optionally supplying an interp_map for the ops *)
let start_interpretation lid dom codom opt_interp_map =
  raise dummy_loc (Failure "start_interpretation") (* FIXME HERE NOW *)
  (*
  let loc = located_loc lid in
  let interp_name = located_elem lid in
  let dom_locref = spec_locref_of_ref dom in
  let dom_spec = lookup_spec dom_locref in
  let codom_locref = spec_locref_of_ref codom in
  let codom_spec = lookup_spec codom_locref in
  let op_param_ids =
    concat_map op_param_ids (List.rev codom_spec.spec_ops) in
  let codom_args = List.map
                     (fun id -> (id, mk_var (loc, id)))
                     op_param_ids in
  (* Hook function that generates an instance id__instance of the domain
  typeclass from the codomain typeclass, when the obligations are done *)
  let hook _ _ =
    reporting_exceptions
      (fun () ->
       ignore
         (add_instance_for_interp
            (* The loc *)
            loc
            (* Instance name: morph_name__instance *)
            (add_suffix interp_name "instance")
            (* Params: the args of codom plus a codom instance *)
            (List.map mk_implicit_var_assum op_param_ids
             @ [mk_implicit_assum
                  (Id.of_string "Spec")
                  (mk_ref_app_named_args
                     loc
                     (spec_typeclass_ref loc codom_locref)
                     codom_args)])
            (* Domain globref *)
            (lookup_spec_globref (spec_locref_of_ref dom))
            (* Interpretation: the one we just added *)
            (mk_var (loc, interp_name))
            (* Co-domain spec ops: codom.codom__ops *)
            (mk_ref_app_named_args
               loc
               (spec_ops_ref loc codom_locref)
               codom_args)
            (* Co-domain spec model: proj1 spec_models_iso Spec *)
            (mkAppC (mk_reference ["Coq"; "Init"; "Logic"] "proj1",
                     [mk_specware_ref "spec_models_iso";
                      mk_var (loc, Id.of_string "Spec")]))))
  in
  let interp_tp = mkAppC (mk_specware_ref "Interpretation",
                          [mkRefC (spec_repr_ref (qualid_of_reference dom));
                           mkRefC (spec_repr_ref (qualid_of_reference codom))])
  in
  match opt_interp_map with
  | None -> start_definition ~hook lid [] interp_tp
  | Some interp_map ->
     let ops_id = Id.of_string "ops" in
     let opCons_ref =
       Qualid (loc, mk_qualid specware_mod "opCons") in
     let tt_ref =
       Qualid (loc, mk_qualid ["Coq"; "Init"; "Datatypes"] "tt") in
     (* Build a pattern to match nested dependent pairs for codom_spec's ops;
     the returned add_lets function adds let-bindings for the defined ops *)
     let (codom_ops_pattern, add_codom_lets) =
       (* Remember: we fold left here because ops are in reverse order *)
       List.fold_left
         (fun (pat,add_lets) op ->
          let (op_id, op_tp, oppred) = op in
          let field_id =
            if oppred_is_eq oppred then field_var_id op_id else op_id in
          (CPatCstr (loc, opCons_ref, [],
                     [CPatAtom (loc, Some (Ident (loc, field_id)));
                      CPatAtom (loc, Some (Ident (loc, field_proof_id op_id)));
                      pat]),
           match oppred with
           | Pred_Eq eq_expr ->
              (fun expr ->
               mkLetInC ((loc, Name op_id), eq_expr, add_lets expr))
           | _ -> add_lets))
         (CPatAtom (loc, Some tt_ref), fun expr -> expr)
         codom_spec.spec_ops
     in
     (* Build nested dependent pairs for the ops of dom_spec *)
     let dom_ops_expr =
          List.fold_left
            (fun expr op ->
             let (op_id, _, _) = op in
             mkAppC (mkRefC opCons_ref,
                     [apply_interp_map loc interp_map op_id;
                      mk_named_hole loc (field_proof_id op_id);
                      expr]))
            (mk_reference ["Coq"; "Init"; "Datatypes"] "tt")
            dom_spec.spec_ops
     in
     (* Build a tactic expression to call interp_tactic *)
     let tactic =
       Tacexpr.TacArg
         (loc,
          Tacexpr.TacCall
            (loc,
             ArgArg (loc, Nametab.locate_tactic
                            (mk_qualid specware_mod "interp_tactic")),
             []))
     in
     (* Start the Program Definition of the interpretation *)
     add_program_definition
       ~hook ~tactic
       lid [] (Some interp_tp)
       (mkAppC
          (mk_specware_ref "mkInterp",
           [mkLambdaC
              ([loc, Name ops_id], Default Explicit,
               mkAppC (mk_specware_ref "spec_ops",
                       [mkRefC (spec_repr_ref (loc, codom_locref))]),
               CCases (loc, RegularStyle, None,
                       [mk_var (loc, ops_id), (None, None)],
                       [loc,
                        [loc, [codom_ops_pattern]],
                        CCast
                          (loc,
                           add_codom_lets dom_ops_expr,
                           CastConv
                             (mkAppC
                                (mk_specware_ref "spec_ops",
                                 [mkRefC (spec_repr_ref (loc, dom_locref))])))]));
            mk_named_hole loc (Id.of_string "model_f")]))
   *)

(* Start an interactive definition of an instance id__instance from the
typeclass of codom to that of dom, and then generate an interpretation id from
that instance. *)
(*
let start_interp_instance lid dom codom interp_map =
  let loc = located_loc lid in
  let id = located_elem lid in
  let dom_locref = spec_locref_of_ref dom in
  let dom_spec = lookup_spec dom_locref in
  let codom_locref = spec_locref_of_ref codom in
  let codom_spec = lookup_spec codom_locref in
  let op_param_ids =
    concat_map op_param_ids (List.rev codom_spec.spec_ops) in
  let codom_args = List.map
                     (fun id -> (id, mk_var (loc, id)))
                     op_param_ids in
  (* Start a section id__instance_section *)
  let _ = begin_section (add_suffix id "instance_section") in
  (* Import the codomain spec's module *)
  let _ = Library.import_module false (qualid_of_reference codom) in
  (* Hook function that gets called when the instance is complete: creates an
  interpretation named id from the instance *)
  let hook =
    (fun _ ->
     reporting_exceptions
       (fun () ->
        (* End the section started above *)
        let _ = end_section () in
        FIXME HERE NOW
        ))
  in
  begin_instance
    ~hook
    [LocalRawAssum ([Id.of_string "H"],
                    Generalized (Implicit, Implicit, b),
                    mkRefC (spec_typeclass_ref loc codom_locref))]
    (loc, add_suffix id "instance")
    FIXME HERE NOW
 *)


  (***
   *** Spec Imports
   ***)

(* FIXME: hints are not currently used; they also assume that subtype predicates
are classes, which they currently are not... *)

let add_import_hints loc free_vars hole_map imp =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let imp_spec_locref = spec_globref_to_locref imp.spec_import_globref in

  (* Helper to build a refine hint *)
  let mk_refine_hint id constr =
    let glob = replace_glob_free_vars
                 hole_map
                 (Detyping.detype true free_vars env evd constr)
    in
    let tacexpr =
      (*
      (Tacexpr.TacML
         (loc,
          {Tacexpr.mltac_tactic = "refine";
           Tacexpr.mltac_plugin = "extratactics"},
          [Genarg.in_gen
             (Genarg.glbwit Constrarg.wit_constr)
             (glob, None)]
      )) *)
      (Tacexpr.TacArg
           (loc,
            Tacexpr.TacCall
              (loc, ArgArg (loc, Nametab.locate_tactic
                                   (qualid_of_ident (Id.of_string "specware_refine"))),
               [Tacexpr.ConstrMayEval (ConstrTerm (glob, None))]
      )))
    in
    let _ = debug_printf 1 "@[hint tactic: %a@]\n"
                         pp_autotactic (Hints.Extern tacexpr) in
    Hints.HintsExternEntry
      (1,
       Some ([], Pattern.PRef
                   (try Nametab.locate
                          (field_in_spec imp_spec_locref id)
                    with Not_found ->
                      raise dummy_loc (Failure "add_import_hints"))),
       tacexpr)
  in

  (* Add the op hints *)
  let _ = add_typeclass_hints
            (concat_map
               (fun (op_id, op_constr, oppred) ->
                mk_refine_hint (field_class_id op_id) op_constr
                ::(match oppred with
                   | Pred_Trivial -> []
                   | Pred_Eq op_pf_constr ->
                      [mk_refine_hint (field_pred_id op_id) op_pf_constr]
                   | Pred_Fun op_pf_constr ->
                      [mk_refine_hint (field_pred_id op_id) op_pf_constr]))
               imp.spec_import_op_constrs)
  in

  (* Build the constr Build_spec op1 ... opn ax_proof1 ... ax_proofn *)
  (*
  let spec_args =
    List.fold_right
      (fun (op_id, op_constr, op_pf_constr_opt) args ->
       op_constr::
         (match op_pf_constr_opt with
          | None -> args
          | Some op_pf_constr -> op_pf_constr::args))
      imp.spec_import_op_constrs
      (List.map snd imp.spec_import_axiom_constrs) in
  let builder_ctor =
    match Nametab.locate (spec_typeclass_builder_qualid imp_spec_locref) with
    | ConstructRef ctor -> ctor
    | _ -> raise loc (Failure "add_import_hints")
  in
  let spec_constr =
    Term.mkApp (Term.mkConstruct builder_ctor,
                Array.of_list spec_args) in
  (* Now add spec_constr as a hint for building the imported spec *)
  add_typeclass_hints
    [mk_refine_hint (spec_locref_basename imp_spec_locref) spec_constr]
   *)
  ()

let add_import_group_hints loc impgrp =
  let env = Global.env () in

  (* Build a list of all the fields in the current spec that might be involed,
  paired with the id for the respective class of each id *)
  let free_var_class_list =
    concat_map
      (fun (op_id, has_oppred) ->
       (field_param_id op_id, field_class_id op_id)
       ::(if has_oppred then
            [field_proof_id op_id, field_pred_id op_id]
          else []))
      impgrp.spec_impgrp_ops
    @ List.map
        (fun ax_id -> (ax_id, field_class_id ax_id))
        impgrp.spec_impgrp_axioms
  in
  let free_vars = List.map fst free_var_class_list in
  (* Build a map from each free variable f__param or f__proof to the hole
     (_:f__class) or (_:f__pred), respectively *)
  let add_hole_map_binding map (id, tp_id) =
    let tp_glob =
      (Constrintern.intern_constr
         env
         (mk_var (loc, tp_id))) in
    let _ = debug_printf 1 "@[tp_glob: %a@]\n" pp_glob_constr tp_glob in
    Id.Map.add id (mk_glob_cast loc (mk_glob_hole loc) tp_glob) map
  in
  let hole_map =
    List.fold_left add_hole_map_binding Id.Map.empty free_var_class_list
  in

  (* Now call add_import_hints for each import in this group *)
  List.iter (add_import_hints loc free_vars hole_map)
            impgrp.spec_impgrp_imports


(* Import a spec that is constructed by a RefinementOf expression *)
let import_refinement_constr_expr loc constr_expr =
  (* Get the current Coq context *)
  let (evd,env) = Lemmas.get_current_context () in
  (* Internalize constr_expr into a construction *)
  let (constr,_) = Constrintern.interp_constr env evd constr_expr in
  let constr_hnf = hnf_constr constr in
  (* Destruct constr as a RefinementOf object *)
  let ((ops,axioms),_,imports) = destruct_refinementof constr_hnf in
  (* Get a fresh import number in the current spec *)
  let imp_num = find_unused_import_id (get_current_spec loc) in

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

  (* Helper function to fold occurrences of "f__param" into just "f" and to fold
  "def f__param f__proof" into f (Coq's built-in fold does not seem to work) *)
  (* FIXME: remove ids from op_ids and eq_ids when going inside binders *)
  let rec fold_defs op_ids eq_ids constr =
    let recurse () = Term.map_constr (fold_defs op_ids eq_ids) constr in
    match Term.kind_of_term constr with
    | Term.App (head, args) ->
       let args_len = Array.length args in
       if (constr_is_constant
             (mk_constant specware_mod "def") head)
          && args_len >= 4 then
         (match Term.kind_of_term args.(3) with
          | Term.Var f__proof ->
             (match match_proof_id f__proof with
              | Some f ->
                 if Id.Set.mem f eq_ids then
                   Term.mkApp (Term.mkVar f,
                               Array.map
                                 (fold_defs op_ids eq_ids)
                                 (Array.sub args 4 (args_len - 4)))
                 else recurse ()
              | None -> recurse ())
          | _ -> recurse ())
       else recurse ()
    | Term.Var f__param ->
       (match match_param_id f__param with
        | Some f ->
           if Id.Set.mem f eq_ids then
             Term.mkVar (field_var_id f)
           else if Id.Set.mem f__param op_ids then
             Term.mkVar f
           else constr
        | _ -> constr)
    | _ -> recurse ()
  in
  let extern_with_folds op_ids eq_ids constr =
    Constrextern.extern_constr true env evd (fold_defs op_ids eq_ids constr)
  in

  (*** Add definitions that contain the RefinementOf object itself as well as
  ops and a model of the ref_spec of this RefinementOf object. NOTE: we do this
  before adding the ops / axioms to the current spec, since having the latter in
  the context seems to make things slow... ***)

  (* Add a definition spec__import<i> := constr_expr *)
  let _ = add_definition (loc, spec_import_id imp_num) [] None constr_expr in
  (* Add spec_model__import<i> : spec_model (ref_spec _ spec__import<i>) := ... *)
  let op_param_ids = (concat_map op_param_ids ops) in
  let ops_expr =
    List.map (map_op (Constrextern.extern_constr true env evd)) ops in
  let op_param_vars = mk_vars loc op_param_ids in
  let op_param_set = Id.Set.of_list op_param_ids in
  let axiom_params =
    List.map (fun (ax_id, ax_tp) ->
              mk_explicit_assum
                (field_param_id ax_id)
                (Constrextern.extern_constr true env evd ax_tp))
             axioms in
  let _ = add_definition
            (loc, spec_import_model_id imp_num)
            []
            (Some
               (forall_ops
                  loc ops_expr
                  (mkCProdN
                     loc axiom_params
                     (mkAppC
                        (mk_specware_ref "spec_model",
                         [mkAppC (mk_specware_ref "ref_spec",
                                  [mk_hole loc;
                                   mk_var (loc, spec_import_id imp_num)])])))))
            (lambda_ops loc ops_expr
                        (mkCLambdaN loc axiom_params
                                    (make_model_constr_expr loc axioms))) in
  (* Build the expr (spec_model__import<i> <op params> <axiom params>) *)
  let spec_model_expr =
    mkAppC (mk_var (loc, spec_import_model_id imp_num),
            op_param_vars
            @ (List.map (fun (ax_id,_) ->
                         mk_var (loc, field_param_id ax_id)) axioms)) in

  (*** Now we add the imported ops and axioms to the current spec ***)

  (* Add all the ops specified by constr *)
  let eq_ids =
    List.fold_left
      (fun eq_ids (f,tp,oppred) ->
       let _ =
         add_spec_field false (loc, f)
                        (extern_with_folds op_param_set eq_ids tp)
                        (map_oppred (extern_with_folds op_param_set eq_ids) oppred) in
       if oppred_is_eq oppred then Id.Set.add f eq_ids else eq_ids)
      Id.Set.empty
      ops
  in
  (* Add all the axioms specified by constr *)
  let _ =
    List.iter
      (fun (ax_name,ax_tp) ->
       add_spec_field true
                      (loc, ax_name)
                      (extern_with_folds op_param_set eq_ids ax_tp)
                      Pred_Trivial)
      axioms
  in

  (*** Now we build the instances ***)

  (* Get the Coq context again, to have the ops and axioms in the context *)
  (*
  let env = Global.env () in
  let evd = Evd.from_env env in
   *)

  (* Interpret the value of spec_ops__import<i> to a constr *)
  (*
  let ops_constr =
    hnf_constr
      (fst (Constrintern.interp_constr env evd spec_ops_expr))
  in
   *)
  (* Interpret the value of spec_model__import<i> to a constr *)
  (*
     let model_constr =
       compute_constr
         (fst (Constrintern.interp_constr
                 env_with_axs evd (mk_var (loc, spec_import_model_id imp_num))))
     in
   *)

  (* Add the typeclass instances, while building the spec_imports list *)
  let spec_imports =
    List.mapi
      (fun j refimp ->

       (* Add spec__import<i>__interp<j> :
            Interpretation <import spec j> (ref_spec _ spec__import<i>) *)
       let _ =
         ignore
           (add_definition_constr
              (spec_import_interp_id imp_num j)
              (Some
                 (Term.mkApp
                    (Term.mkConst
                       (mk_constant specware_mod "Interpretation"),
                     [| Term.mkConst (global_spec_repr_constant
                                        loc refimp.ref_import_fromspec);
                        Term.mkApp
                          (Term.mkConst
                             (mk_constant specware_mod "ref_spec"),
                           [| Term.mkConst (global_spec_repr_constant
                                              loc src_spec_globref);
                              Term.mkConst
                                (mk_constant []
                                             (Id.to_string
                                                (spec_import_id imp_num)))
                             |])|])))
              (refimp.ref_import_interp, Evd.empty_evar_universe_context))
       in

       (* Add instance spec__import<i>__instance<j> *)
       let imp_op_constrs =
         add_instance_for_interp
           loc (spec_import_instance_id imp_num j)
           (* Parameters: the axiom typeclasses *)
           (List.map
              (fun (ax_id, _) ->
               (mk_implicit_assum
                  (field_param_id ax_id)
                  (mk_var (loc, field_class_id ax_id))))
              axioms)
           (* Domain spec *)
           refimp.ref_import_fromspec
           (* Co-domain spec: the ref_spec of spec__import<i> *)
           (*
           (Term.mkApp
              (Term.mkConst (mk_constant specware_mod "ref_spec"),
               [| Term.mkConst (global_spec_repr_constant
                                  loc src_spec_globref);
                  Term.mkVar (spec_import_id imp_num) |]))
            *)
           (* Interpretation: spec__import<i>__interp<j> *)
           (mk_var (loc, spec_import_interp_id imp_num j))
           (* The model of the co-domain spec *)
           spec_model_expr
       in

       (* Build (map_model interp spec_ops__import<i> spec_model__import<i>)
          to get the proofs of the imp_spec axioms in the current spec *)
       (*
          let imp_ax_proofs_constr =
            compute_constr
              (Term.mkApp
                 (Term.mkConst (mk_constant specware_mod "map_model"),
                  [| Term.mkConst (global_spec_repr_constant
                                     loc refimp.ref_import_fromspec);
                     Term.mkApp
                       (Term.mkConst (mk_constant specware_mod "ref_spec"),
                        [| Term.mkConst (global_spec_repr_constant
                                           loc src_spec_globref);
                           Term.mkVar (spec_import_id imp_num) |]);
                     refimp.ref_import_interp;
                     ops_constr; model_constr |])) in
          let imp_ax_constr_list =
            destruct_constr spec_model_descr imp_ax_proofs_constr
          in
          let _ =
            if List.length imp_ax_constr_list
               = List.length imp_spec.spec_axioms
            then () else
              raise loc (MalformedRefinement
                           (constr, "axiom proofs", imp_ax_proofs_constr))
          in

          (* Build a list that maps each axiom in the imported spec to the
          constrs that build its proof in the current spec *)
          let imp_ax_constrs =
            List.map2
              (fun (ax_id, _) ax_constr -> (ax_id, ax_constr))
              (List.rev imp_spec.spec_axioms) imp_ax_constr_list
          in
        *)

       { spec_import_globref = refimp.ref_import_fromspec;
         spec_import_op_constrs = imp_op_constrs;
         (* spec_import_axiom_constrs = imp_ax_constrs; *)
         spec_import_interp = refimp.ref_import_interp }
      )
      imports
  in

  (* Build the impgrp structure *)
  let impgrp = { spec_impgrp_num = imp_num;
                 spec_impgrp_ops =
                   List.map (fun (op_id,_,oppred) ->
                             (op_id, oppred_is_nontrivial oppred)) ops;
                 spec_impgrp_axioms =
                   List.map (fun (ax_id,_) -> ax_id) axioms;
                 spec_impgrp_imports = spec_imports }
  in
  (*
  let _ = add_import_group_hints loc impgrp in
   *)

  (*** Now add the imports to the current spec, and we are done ***)
  update_current_spec
    loc
    (fun spec ->
     {spec with spec_imports = impgrp::spec.spec_imports})


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


(* Import a spec_term *)
let import_spec_term loc st =
  import_refinement_constr_expr loc (refinement_expr_of_spec_term st)


(***
 *** 
 ***)


(***
 *** Beginning and Ending the Current Spec
 ***)

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
         (fun (op_id, op_tp, oppred) ->
          let op_param =
            mk_implicit_assum (field_param_id op_id)
                              (mk_var (loc, field_class_id op_id)) in
          if oppred_is_nontrivial oppred then
            [op_param; mk_implicit_assum (field_proof_param_id op_id)
                                         (mk_var (loc, field_pred_id op_id))]
          else
            [op_param])
         spec.spec_ops)
  in
  let _ = add_typeclass (loc, spec.spec_name) false true op_params ax_fields in
  (* Build the spec representation spec__Spec *)
  let _ = add_definition_constr (spec_repr_id spec.spec_name) None
                                (build_spec_repr loc spec) in
  (* FIXME HERE NOW: add back the Iso proof!! *)
  (*
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
                         List.concat
                           (List.rev_map
                              (fun op ->
                               List.map (fun id -> mk_var (loc, id))
                                        (op_param_ids op))
                              spec.spec_ops))]))
            (mk_named_tactic_hole
               loc
               (mk_qualid specware_mod "prove_spec_models_iso"))
  in
   *)

  (* Add all hints in the import list to the current module *)
  (* let _ = List.iter (add_import_group_hints loc) spec.spec_imports in *)

  (* Register the current spec *)
  let spec_globref =
    global_modpath (Nametab.locate (qualid_of_ident spec.spec_name))
  in
  let _ = register_spec spec_globref spec in
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
           (fun () -> end_new_spec lspec_name) ]

  (* Start a non-interactive spec definition *)
  | [ "Spec" var(lspec_name) ":=" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [located_elem lspec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            let _ = begin_new_spec lspec_name in
            let _ = import_spec_term dummy_loc st in
            end_new_spec lspec_name) ]

  (* Start a definition of a spec via refinement *)
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

  (* Add a declared op *)
  | [ "Spec" "Variable" var(lid) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field false lid tp Pred_Trivial) ]

  (* Add a declared op with a subtype predicate *)
  | [ "Spec" "Variable" var(lid) ":" constr(tp) "|" constr(pred) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_spec_field false lid tp (Pred_Fun pred)) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" var(lid) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [located_elem lid], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            add_spec_field false lid tp (Pred_Eq body)) ]

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
           (fun () -> add_spec_field true lid tp Pred_Trivial) ]

  (* Add a theorem *)
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

  (* Import a spec using a "raw" expression of type RefinementOf *)
  | [ "Spec" "RawImport" constr(tm) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            import_refinement_constr_expr (constr_loc tm) tm) ]

  (* Import a spec term *)
  (* FIXME: get the location right *)
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term dummy_loc st) ]

  (* Define an interpretation *)
  | [ "Spec" "Interpretation" var(lmorph_name)
             ":" global(dom) "->" global(codom) ":="
             "{" interp_map(imap) "}"]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity,
                                   [located_elem lmorph_name]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> start_interpretation lmorph_name dom codom (Some imap)) ]

  (* Define an interpretation using tactics *)
  | [ "Spec" "Interpretation" var(lmorph_name) ":" global(dom) "->" global(codom) ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity,
                                   [located_elem lmorph_name]),
          Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> start_interpretation lmorph_name dom codom None) ]

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

TACTIC EXTEND my_instantiate_tac
  | [ "my_instantiate" "(" ident(evar_id) ":=" constr(evar_def) ")" ]
    -> [ Proofview.Goal.enter
           (fun gl_nonnorm ->
            let gl = Proofview.Goal.assume gl_nonnorm in
            let env = Proofview.Goal.env gl in
            let evd = Proofview.Goal.sigma gl in
            let evar = Evd.evar_key evar_id evd in

            (* let evd = Evd.define evar evar_def evd in
            Proofview.Unsafe.tclEVARS evd *)

            Evar_tactics.instantiate_tac_by_name
              evar_id
              (Tacinterp.default_ist (),
               Detyping.detype true [] env evd evar_def)
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

(* A vernacular command version of instantiate_record_type *)
VERNAC COMMAND EXTEND Instantiate_record_type_vernac
  | [ "Instantiate" "Record" "Type" var(levar_id) ]
    => [ (Vernacexpr.VtSideff [snd levar_id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            (* Get the current proof state, and look up the evar *)
            let (evd,env) = Lemmas.get_current_context () in
            let (loc,evar_id) = levar_id in
            let evar = Evd.evar_key evar_id evd in

            (* Add a record type for evar *)
            let (evd, rectp_ind, field_evars) =
              add_record_type_for_evar env evd evar in

            (* FIXME HERE NOW *)
            ()
           )]
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

VERNAC COMMAND EXTEND Debug_close_proof
  | [ "Close" "Proof" ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ Proof_global.set_terminator
           (fun _ ->
            ()
              (* raise dummy_loc (Failure "Debug Terminator") *)) ]
END


(* A debug-mode version of Defined *)
VERNAC COMMAND EXTEND Defined_debug
  | [ "Defined_Debug" ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ (* let proof =
           Proof_global.close_proof ~keep_body_ucst_sepatate:false (fun x -> x)
         in *)
         (* Lemmas.save_proof (* ~proof *) (Proved (true, None)) *)
    interp (dummy_loc, VernacEndProof (Proved (true, None)))
 ]
END


(* FIXME: why does this need an argument in order to work...? *)
TACTIC EXTEND pushout_tactics
  | [ "pushout_tactic" constr(s) ]
    -> [ Proofview.Goal.nf_enter
           (fun gl ->
            reporting_exceptions
              (fun () ->
               (* Get the current proof state *)
               let env = Proofview.Goal.env gl in
               let evd = Proofview.Goal.sigma gl in
               let evdref = ref evd in
               let concl = Proofview.Goal.concl gl in

               (* Make sure we have Pushout as the goal, and extract the two
               functions we are trying to unify and their co-domains *)
               let (dom_constr, codom_constr1, codom_constr2,
                    f_constr1, f_constr2) =
                 match Term.kind_of_term concl with
                 | Term.App (head, [| dom_constr; codom_constr1; codom_constr2;
                                      f_constr1; f_constr2 |])
                      when constr_is_inductive
                             (mk_inductive specware_mod "Pushout") head ->
                    (dom_constr, codom_constr1, codom_constr2,
                     f_constr1, f_constr2)
                 | _ ->
                    (* FIXME: is this the right way to fail...? *)
                    raise
                      dummy_loc
                      (Refiner.FailError
                         (0, lazy (str "pushout_tactic applied to a non-Pushout goal")))
               in
               (* let (dom_ops,dom_axioms) = destruct_constr spec_descr dom_constr in *)
               let (codom1_ops,codom1_axioms) =
                 destruct_constr
                   spec_descr
                   (hnf_constr ~env_opt:(Some env) ~evdref_opt:(Some evdref)
                               codom_constr1) in
               let (codom2_ops,codom2_axioms) =
                 destruct_constr
                   spec_descr
                   (hnf_constr ~env_opt:(Some env) ~evdref_opt:(Some evdref)
                               codom_constr2) in

               

               (* FIXME HERE NOW: do this!! *)
               Proofview.tclUNIT ()
           ))]

END
