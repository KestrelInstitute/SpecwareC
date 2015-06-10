
DECLARE PLUGIN "specware"

open Names
open Loc
open Libnames
open Globnames
open Pp
open Errors
open Vernacexpr
open Vernacentries
open Constrexpr
open Misctypes
open Decl_kinds
open Ppconstr
open Genredexpr
open Topconstr

(***
 *** Helper functions
 ***)

let dummy_loc = Loc.ghost

(* Map f over an option type *)
let map_opt f opt =
  match opt with
  | Some x -> Some (f x)
  | None -> None

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
(* FIXME: use sets for deps instead of lists *)
let rec stable_reverse_topo_sort loc key key_eq deps l =
  let arr = Array.of_list l in
  let arr_deps = Array.make (List.length l) [] in
  let visited = Array.make (List.length l) false in
  let rec get_node_by_key_help k j =
    if j > Array.length arr then None
    else if key_eq k (key arr.(j)) then Some j
    else get_node_by_key_help k (j+1) in
  let get_node_by_key k = get_node_by_key_help k 0 in
  (* Perform a DFS to build the transitive closure of deps *)
  let rec build_node_deps path_to_i i =
    if visited.(i) then
      arr_deps.(i)
    else if List.mem i path_to_i then
      raise loc (TopoCircularity i)
    else
      let i_immed_deps = filter_map get_node_by_key (deps arr.(i)) in
      let i_deps = concat_map (build_node_deps (i::path_to_i)) i_immed_deps in
      visited.(i) <- true;
      arr_deps.(i) <- i_deps;
      i::i_deps
  in
  let _ = for i = 0 to Array.length arr_deps - 1 do
            ignore (build_node_deps [] i)
          done in
  let index_arr = Array.init (List.length l) (fun i -> i) in
  let _ = Array.stable_sort
            (fun i j ->
             if List.mem j arr_deps.(i) then 1
             else if List.mem i arr_deps.(j) then -1
             else j-i)
            index_arr in
  Array.to_list (Array.map (fun i -> arr.(i)) index_arr)


(***
 *** Helper functions for interacting with Coq
 ***)

(* Syntactic expressions for the sorts Type and Prop *)
let type_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GType [])
let prop_expr = Constrexpr.CSort (Loc.dummy_loc, Misctypes.GProp)

(* Pretty-print a term (a "construction") *)
let pp_constr fmt c = Pp.pp_with fmt (Printer.pr_constr c)

(* Pretty-print a term *)
let pp_constr_expr fmt c = Pp.pp_with fmt (Richpp.pr_constr_expr c)

(* Pretty-print a vernacular command *)
let pp_vernac fmt cmd = Pp.pp_with fmt (Ppvernac.Richpp.pr_vernac_body cmd)

(* Convert a term to a string *)
let constr_expr_to_string c = Pp.string_of_ppcmds (Richpp.pr_constr_expr c)

(* Accessors for located types *)
let located_elem (x : 'a located) = snd x
let located_loc (x : 'a located) = fst x

(* Build a name from an ident *)
let name_of_ident (id : Id.t) : Name.t = Name id

(* Build a located name from a located ident *)
let lname_of_lident (id : lident) : lname =
  (located_loc id, name_of_ident (located_elem id))

(* Test if an identifier has a given prefix, and if so, return the
   rest of the identifier after that prefix *)
let match_prefix id prefix =
  let pre_len = String.length prefix in
  let id_str = Id.to_string id in
  let id_len = String.length id_str in
  if id_len >= pre_len &&
       String.sub id_str 0 pre_len = prefix then
    Some (String.sub id_str pre_len (id_len - pre_len))
  else None

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

(* Build an application *)
let mk_app f args =
  CApp (dummy_loc, (None, f),
        List.map (fun arg -> (arg, None)) args)

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
  make_qualid (DirPath.make ([mod_name] @ DirPath.repr mod_path)) id

(* Build a term for a global constant, where dir lists the module path
   as a list (e.g., ["Coq"; "Init"; "Logic"]) and id is the id *)
let mk_reference dir id =
  CRef (Qualid (dummy_loc, mk_qualid dir id), None)

(* Get a string for a global reference *)
let global_to_string gr =
  match gr with
  | VarRef v -> raise dummy_loc (Failure "global_to_string")
  | ConstRef c -> Constant.to_string c
  | IndRef (i,_) -> MutInd.to_string i
  | ConstructRef _ -> raise dummy_loc (Failure "global_to_string")

(* Get the module for a global reference *)
let global_modpath gr =
  match gr with
  | VarRef _ -> raise dummy_loc (Failure "global_modpath")
  | ConstRef c -> Constant.modpath c
  | IndRef (i, _) -> MutInd.modpath i
  | ConstructRef ((i, _), _) -> MutInd.modpath i

(* Turn a global reference into a local one *)
(* FIXME: find a better way than using strings! *)
let qualid_of_global gr =
  qualid_of_string (global_to_string gr)

(* Build an expression for a global applied to named implicit args *)
let mk_global_app_named_args gr args =
  mk_ref_app_named_args (Qualid (dummy_loc, qualid_of_global gr)) args

(* Build an exprssion for a global with @ in front of it *)
let mk_global_expl gr =
  CAppExpl (dummy_loc,
            (None, (Qualid (dummy_loc, qualid_of_global gr)), None),
            [])

(* Look up a defined constant by qualid *)
(* FIXME: raise a different exception if the qualid is not a constant... *)
let lookup_constant loc qualid =
  match Nametab.locate qualid with
  | ConstRef c -> c
  | _ -> raise loc Not_found

(* Look up an identifier in the current module and make it fully qualified *)
let qualify_identifier id =
  qualid_of_global (Nametab.locate (qualid_of_ident id))

(* Build the expression t1 = t2 *)
let mk_equality t1 t2 =
  CApp (dummy_loc,
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
   normal type-class in Prop (if false), and fields is a list of
   triples (id, type, coercion_p) to be passed to mk_record_field *)
let add_typeclass class_id is_op_class is_prop_class params fields =
  let cmd =
    VernacInductive (false, BiFinite,
                     [((false, class_id), params,
                       Some (if is_prop_class then prop_expr else type_expr),
                       Class is_op_class,
                       if is_op_class then
                         match fields with
                         | [] -> Constructors []
                         | [(id, tp, _)] ->
                            Constructors [false, (id, tp)]
                         | _ -> raise (located_loc class_id) (Failure "add_typeclass")
                       else
                         RecordDecl (None, List.map mk_record_field fields)),
                      []])
  in
  let _ = Format.eprintf "add_typeclass command:\n%a" pp_vernac cmd in
  interp (located_loc class_id, cmd)

(* Add an instance of an operational typeclass *)
let add_op_instance inst_name inst_params inst_tp inst_body =
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Decl_kinds.Explicit, inst_tp),
               Some (false, inst_body),
               None)
  in
  let _ = Format.eprintf "add_op_instance command:\n%a" pp_vernac cmd in
  interp (located_loc inst_name, cmd)


(* Add an instance using the given record fields *)
let add_record_instance inst_name inst_params inst_tp inst_fields =
  let loc = located_loc inst_name in
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Decl_kinds.Explicit, inst_tp),
               Some (true,
                     CRecord (loc, None,
                              List.map (fun (id,body) -> (Ident (loc, id),body))
                                       inst_fields)),
               None)
  in
  let _ = Format.eprintf "add_record_instance command:\n%a" pp_vernac cmd in
  interp (loc, cmd)

(* Begin an interactively-defined instance *)
let begin_instance inst_name inst_params inst_tp =
  let loc = located_loc inst_name in
  interp (loc, VernacInstance
                 (false, inst_params,
                  (inst_name, Decl_kinds.Explicit, inst_tp),
                  None, None))

(* Begin a new module *)
let begin_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []))

(* End the current module, which should have name mod_name *)
let end_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacEndSegment mod_name)

(* Perform some operation(s) inside a newly-defined module *)
let within_module mod_name f =
  let _ = begin_module mod_name in
  let ret = f () in
  let _ = end_module mod_name in
  ret

(* Check that two terms are definitionally equal relative to the given
   parameter list, by checking that (forall params, eq_refl : t1=t2)
   is well-typed (eq_refl is the constructor for the equality type) *)
(* FIXME: make sure this works! *)
let check_equal_term params t1 t2 =
  try
    interp
      (dummy_loc,
       VernacCheckMayEval
         (None, None,
          (Constrexpr_ops.mkCProdN
             dummy_loc
             params
             (CCast (dummy_loc,
                     CApp (dummy_loc,
                           (None, mk_reference ["Coq"; "Init"; "Logic"]
                                               (Id.of_string "eq_refl")),
                           [(t1, None)]),
                     CastConv (mk_equality t1 t2))))));
    true
  with UserError _ -> false

(* Apply a series of reductions to a term in a parameter context, by
   interpreting the term to a constr, applying the reductions in order, and then
   going back to a term *)
let reduce_term params reds t =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let impls, ((env, ctx), imps1) =
    Constrintern.interp_context_evars env evdref params in
  let interp_term t = fst (Constrintern.interp_constr env !evdref t) in
  let uninterp_term c =
    Constrextern.with_implicits
      (Constrextern.with_arguments
         (Constrextern.extern_constr true env !evdref)) c
  in
  let apply_redexpr c r =
    let (evd,r_interp) = Tacinterp.interp_redexp env !evdref r in
    let _ = evdref := evd in
    snd (fst (Redexpr.reduction_of_red_expr env r_interp) env !evdref c) in
  uninterp_term (List.fold_left apply_redexpr (interp_term t) reds)

(* Fold some set of variables in c into equivalent terms, by taking
   folds_c, a list of pairs of constrs (c_from,c_to) where c_from is
   always a variable, and replacing all subterms of c equal to some
   c_from in folds_c with the corresponding c_to. *)
let rec fold_constr_vars folds_c c =
  (* apply_fold_var searches for a constr on the LHS of folds_c that
     equals c, and replaces c by the correponding RHS if found *)
  let rec apply_fold_var folds_c c =
    match folds_c with
    | [] -> c
    | (c_from,c_to)::folds_c' ->
       if Constr.equal c c_from then c_to else apply_fold_var folds_c' c in
  (* Lift a folding, due to a variable binding *)
  let lift_folding folds_c =
    List.map (fun (c_from,c_to) ->
              (Vars.lift 1 c_from, Vars.lift 1 c_to)) folds_c in
  (* The main body: recursively apply folds_c to the subterms of c *)
  match Constr.kind c with
  | Constr.Var _ -> apply_fold_var folds_c c
  | Constr.Rel _ -> apply_fold_var folds_c c
  | _ -> Constr.map_with_binders lift_folding fold_constr_vars folds_c c

(* Unfold the list of global references (which must all be constants,
   i.e., not constructors or type constructors), and then apply the
   given folds, which are given as a list of pairs (var,term) of a
   variable to be folded into the corresponding term (which should be
   equal). All terms are relative to the given parameters. *)
let unfold_fold_term params unfolds folds t =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let impls, ((env, ctx), imps1) =
    Constrintern.interp_context_evars env evdref params in
  let interp_term t = fst (Constrintern.interp_constr env !evdref t) in
  let uninterp_term c = Constrextern.extern_constr true env !evdref c in
  let t_constr = interp_term t in

  (* The following block of code comes from vernac_check_may_eval *)
  (*
  let sigma', t_constr = Constrintern.interp_open_constr env !evdref t in
  let sigma' = Evarconv.consider_remaining_unif_problems env sigma' in
  Evarconv.check_problems_are_solved env sigma';
  let sigma',nf = Evarutil.nf_evars_and_universes sigma' in
  let uctx = Evd.universe_context sigma' in
  let env_bl = Environ.push_context uctx env in
  let t_constr = nf t_constr in
  let _ = evdref := sigma' in
   *)

  let unfold_redfun =
    Tacred.unfoldn
      (List.map (fun gr ->
                 match gr with
                 | ConstRef c -> (Locus.AllOccurrences, EvalConstRef c)
                 | _ -> raise dummy_loc (Failure "unfold_fold_term"))
                unfolds) in
  let constr_unfolded = unfold_redfun env !evdref t_constr in

  (* This used the fold reduction, which seemed to not work right... *)
  (*
  let fold_redfun =
    Tacred.fold_commands
      (List.map (fun t -> fst (Constrintern.interp_constr env !evdref t)) folds) in
  let constr_out =
    fold_redfun env !evdref constr_unfolded in
   *)

  (* This does our own fold, defined above *)
  let folds_c =
    List.map (fun (id,t) ->
              let res_from = interp_term (mk_var (dummy_loc, id)) in
              let res_to = interp_term t in
              (*
              let _ =
                Format.eprintf "\nunfold_fold_term: unfolding %s to %a"
                               (Id.to_string id)
                               pp_constr_expr (uninterp_term res_to) in
               *)
             (res_from, res_to)) folds in
  let constr_out = fold_constr_vars folds_c constr_unfolded in
  let res = uninterp_term constr_out in
  (*
  let _ = Format.eprintf "\nunfold_fold_term: unfolded term: %a\n" pp_constr_expr
                         (uninterp_term constr_unfolded) in
   *)
  let _ = Format.eprintf "\nunfold_fold_term: returning %a\n" pp_constr_expr res in
  res

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
 *** Identifier Suffixes
 ***)

(* Build the identifier used to quantify over a field as a local
   variable *)
let field_var_id f = add_suffix f "param"

(* Get the identifier used locally for the type of a field *)
let field_type_id f = add_suffix f "type"

(* Get the identifier used locally for the type-class of a field *)
let field_class_id f = add_suffix f "class"

(* The name of the instance associated with a field *)
let field_inst_id f = add_suffix f "inst"

(* The axiom typeclass field pointing to an instance of this axiom *)
let field_axelem_id f = add_suffix f "axiom"


(***
 *** Field Terms and Substitutions
 ***)

(* A field term (or term used in a spec field) is a essentially an expression
with a set of its free variables marked as fields. To make substitution of
fields easier, the fields of a field term are represented as the domain of
a substitution into that expression. *)
type field_term =
    { field_term_body : constr_expr;
      field_term_subst : field_subst }

(* A field substitution maps field names to field names, possibly adding
definitions to fields *)
 and field_subst = (Id.t * Id.t * field_term option) list

(* Make the identity substitution on the given fields *)
let mk_id_subst fields = List.map (fun id -> (id, id, None)) fields

(* Make a field term from a constr_expr and a list of potential fields *)
(* FIXME HERE NOW: don't qualify things like f__class *)
let mk_field_term fields body =
  (*
  let free_vars = free_vars_of_constr_expr body in
  let true_fields = List.filter (fun v -> Id.Set.mem v free_vars) fields in
   *)
  let rec fixup_free_vars var_set = function
    | CRef (Ident (loc,id),us) as expr ->
       if Id.Set.mem id var_set then expr else
         CRef (Qualid (loc, qualify_identifier id), us)
    | expr ->
       map_constr_expr_with_binders Id.Set.add fixup_free_vars var_set expr
  in
  { field_term_body = fixup_free_vars (Id.Set.of_list fields) body;
    field_term_subst = mk_id_subst fields }

(* Make the substitution that adds definition d to id for each (id,d) in defs *)
let make_subst_for_defs fields defs : field_subst =
  List.map (fun (id, d) -> (id, id, Some d)) defs

(* Apply a field substitution to a field, returning a pair of the new field name
and the added definition for that field, if any *)
let rec subst_id subst id =
  match subst with
  | [] -> (id, None)
  | (id_from, id_to, defn_opt) :: subst' ->
     if Id.equal id_from id then (id_to, defn_opt) else subst_id subst' id

(* Get the free fields in a field term, i.e., the free variables that are
intended to be used as fields *)
let rec field_term_free_fields t =
  field_subst_free_fields t.field_term_subst
and field_subst_free_fields subst =
  List.fold_left (fun fs (_, id_to, defn_opt) ->
                  Id.Set.add id_to
                             (match defn_opt with
                              | Some defn -> Id.Set.union fs (field_term_free_fields defn)
                              | None -> fs))
                 Id.Set.empty subst

(* The "top-level" free fields of a field term *)
let field_term_top_free_fields t =
  List.map (fun (_, id_to, _) -> id_to) t.field_term_subst

(* Convert a field substitution to a map from Ids to constr_exprs *)
let field_subst_to_id_map subst =
  List.fold_left (fun id_map (id_from, id_to, _) ->
                  Id.Map.add id_from id_to id_map) Id.Map.empty subst

(* Convert a field_term to a constr_expr by applying the substitution *)
let rec field_term_to_expr t =
  replace_vars_constr_expr (field_subst_to_id_map t.field_term_subst)
                           t.field_term_body

(* An attempt to define the given field when it is already defined *)
exception FieldAlreadyDefined of Id.t

(* Apply a field substitution to a field term *)
let rec subst_field_term (subst: field_subst) t =
  { t with field_term_subst = compose_substs subst t.field_term_subst }

(* Compose a substitution with another one *)
and compose_substs (s2 : field_subst) (s1 : field_subst) : field_subst =
  List.map (fun (id_from, id_to, defn_opt) ->
            let (id_to_out, defn_opt') = subst_id s2 id_to in
            let defn_opt_out =
              match (defn_opt, defn_opt') with
              | (Some defn, None) -> Some (subst_field_term s2 defn)
              | (None, _) -> defn_opt'
              | _ ->
                 (* NOTE: this should never happen: should be caught earlier *)
                 raise dummy_loc (FieldAlreadyDefined id_to)
            in
            (id_from, id_to_out, defn_opt_out)) s1
  (* Any fields not already mapped by s1 can be mapped by s2 *)
  @ List.filter (fun (id, _, _) ->
                 not (List.exists (fun (id', _, _) -> Id.equal id id') s1)) s2


(***
 *** Field Contexts
 ***)

(* A field context specifies a list of named fields, each of which has a type
   and an optional definition. Fields can also be marked as "ghost fields",
   meaning that they are actually derived from other fields (e.g., equality
   axioms being derived from defined fields).

   NOTE: field contexts are stored backwards, in that the "earlier" fields are
   stored later in the list; i.e., fields can only refer to fields later in a
   field context. This is to make it easy to add new fields as we go *)
type fctx_elem =
    { felem_id : Id.t;
      felem_is_ghost : bool;
      felem_type : field_term;
      felem_defn : field_term option
    }
type fctx = fctx_elem list

(* Return true iff an fctx_elem is defined *)
let fctx_elem_has_def elem =
  match elem.felem_defn with
  | Some _ -> true
  | None -> false

(* Get the fields referenced by the args in an fctx_elem *)
let fctx_elem_free_fields elem =
  let deps_tp = field_term_free_fields elem.felem_type in
  match elem.felem_defn with
  | Some d -> Id.Set.union deps_tp (field_term_free_fields d)
  | None -> deps_tp

(* Find a named field in an fctx, returning None if not found *)
let rec fctx_lookup fctx f =
  match fctx with
  | [] -> None
  | elem :: fctx' ->
     if Id.equal f elem.felem_id then
       Some elem
     else
       fctx_lookup fctx' f

(* Print an fctx_elem to a string, for debugging purposes *)
let fctx_elem_to_string elem : string =
  match elem.felem_defn with
  | None ->
     Format.sprintf "%s : %s" (Id.to_string elem.felem_id)
                    (constr_expr_to_string
                       (field_term_to_expr elem.felem_type))
  | Some defn ->
     Format.sprintf "%s : %s := %s" (Id.to_string elem.felem_id)
                    (constr_expr_to_string
                       (field_term_to_expr elem.felem_type))
                    (constr_expr_to_string
                       (field_term_to_expr defn))

(* Print an fctx to a string, for debugging purposes *)
let rec fctx_to_string ?(recursive_p=false) fctx =
  if recursive_p then
    match fctx with
    | [] -> ""
    | [elem] -> fctx_elem_to_string elem
    | elem :: fctx' ->
       Format.sprintf "%s, %s" (fctx_elem_to_string elem)
                      (fctx_to_string ~recursive_p:true fctx')
  else
    Printf.sprintf "{%s}" (fctx_to_string ~recursive_p:true fctx)

(* Build a field_term relative to an fctx *)
let mk_fctx_term fctx body =
  mk_field_term (List.map (fun elem -> elem.felem_id) fctx) body

(* Cons a field to a field context *)
let fctx_cons id is_ghost tp defn_opt fctx =
  { felem_id = id; felem_is_ghost = is_ghost;
    felem_type = tp; felem_defn = defn_opt } :: fctx

(* Convert a single fctx_elem to an implicit class assumption *)
let fctx_elem_to_param loc elem =
  mk_implicit_assum (field_var_id elem.felem_id)
                    (mk_var (loc, field_class_id elem.felem_id))

(* Filter out only the non-ghost elements of an fctx *)
let fctx_non_ghosts fctx =
  filter_map (fun elem -> if elem.felem_is_ghost then None else Some elem) fctx

(* Convert an fctx to a list of class parameters, one for each field
   in the context (remember: fctx is reversed) *)
let fctx_params loc fctx =
  List.rev_map (fctx_elem_to_param loc) fctx

(* Check the equality of two field terms relative to fctx *)
let check_equal_field_term loc fctx d1 d2 =
  check_equal_term (fctx_params loc fctx)
                   (field_term_to_expr d1) (field_term_to_expr d2)

(* Apply f to any field name shared by fctx1 and fctx2 *)
let fctx_iter_shared_fields f fctx1 fctx2 =
  List.iter (fun elem1 ->
             match fctx_lookup fctx2 elem1.felem_id with
             | Some _ -> f elem1.felem_id
             | None -> ()) fctx1

(* Filter an fctx to include only the given set of fields and all the fields on
which they recursively depend. NOTE: remember that fctxs are stored backwards,
so that fields can only depend on those occuring *later* in the list. *)
let rec filter_fctx fields fctx =
  match fctx with
  | [] -> []
  | elem :: fctx' ->
     if Id.Set.mem elem.felem_id fields
        || Id.Set.mem (field_var_id elem.felem_id) fields
     then
       elem :: filter_fctx (Id.Set.union (fctx_elem_free_fields elem) fields)
                           fctx'
     else
       filter_fctx fields fctx'

(* Add a definition to the current module / spec, relative to the
   given fctx, and return a field_term for the new definition *)
let add_local_definition loc (fctx : fctx) id type_opt body =
  let free_vars =
    match type_opt with
    | Some tp ->
       Id.Set.union (free_vars_of_constr_expr tp) (free_vars_of_constr_expr body)
    | None -> free_vars_of_constr_expr body
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  let _ = add_definition (loc, id) (fctx_params loc fctx_free_vars) type_opt body in
  mk_fctx_term fctx_free_vars body

(* Add an operational type class to the current module / spec, relative to the
   given fctx, and return a field_term for the new type class *)
let add_local_op_typeclass loc fctx id is_prop_class tp =
  let free_vars = free_vars_of_constr_expr tp in
  let _ =
    Format.eprintf "add_local_op_typeclass for id %s: free vars = %s\n"
                   (Id.to_string id)
                   (Id.Set.fold (fun v str ->
                                 Printf.sprintf "%s,%s" (Id.to_string v) str)
                                free_vars "")
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  let _ = add_typeclass (loc, field_class_id id) true is_prop_class
                        (fctx_params loc fctx_free_vars)
                        [((loc, id), tp, false)] in
  mk_fctx_term fctx_free_vars tp

(* Add an operational typeclass instance to the current module / spec *)
let add_local_op_instance loc fctx id tp body =
  let free_vars =
    Id.Set.union (free_vars_of_constr_expr tp) (free_vars_of_constr_expr body)
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  add_op_instance (loc, id) (fctx_params loc fctx_free_vars) tp body

(* Add a record-based typeclass instance to the current module / spec *)
let add_local_record_instance loc fctx id tp fields =
  let free_vars =
    List.fold_left (fun free_vars (_, body) ->
                    Id.Set.union (free_vars_of_constr_expr body) free_vars)
                   (free_vars_of_constr_expr tp) fields
  in
  let fctx_free_vars = filter_fctx free_vars fctx in
  add_record_instance (loc, id) (fctx_params loc fctx_free_vars) tp fields


(***
 *** Merging and substituting into global field contexts
 ***)

(* Either the types (if flag = false) or the definitions (if flag = true) of the
same field are different in two contexts that are supposed to be compatible *)
exception FieldMismatch of Id.t * bool

(* Merge two fctxs, merging any fields that they share. Also check that the two
fctxs are compatible, meaning that any shared fields have the same types and
definitions; raise FieldMismatch if not. *)
let merge_fctxs loc fctx1 fctx2 =
  (* First, build a list of all the field names and their dependencies *)
  let names_and_deps =
    (List.map (fun elem1 ->
               (elem1.felem_id,
                Id.Set.elements
                  (match fctx_lookup fctx2 elem1.felem_id with
                   | Some elem2 -> Id.Set.union (fctx_elem_free_fields elem1)
                                                (fctx_elem_free_fields elem2)
                   | None -> fctx_elem_free_fields elem1)))
              fctx1)
    @ (filter_map (fun elem2 -> match fctx_lookup fctx1 elem2.felem_id with
                                | None -> Some (elem2.felem_id,
                                                Id.Set.elements
                                                  (fctx_elem_free_fields elem2))
                                | Some _ -> None) fctx2)
  in
  (* Next, sort the names *)
  (* FIXME: catch the TopoCircularity exception! *)
  let sorted_names_and_deps =
    stable_reverse_topo_sort loc fst Id.equal snd names_and_deps
  in
  (* Now build up the context to return starting at the right, because fctxs are
  stored in reverse order (inner-most bindings last) *)
  List.fold_right
    (fun (f, _) fctx ->
     let new_elem =
       match (fctx_lookup fctx1 f, fctx_lookup fctx2 f) with
       | (Some elem1, None) -> elem1
       | (None, Some elem2) -> elem2
       | (Some elem1, Some elem2) ->
          (* NOTE: We just sorted the names, so the global_defn_to_term checks
        should not possibly fail... *)
          let _ = if not (check_equal_field_term loc fctx elem1.felem_type
                                                 elem2.felem_type) then
                    raise loc (FieldMismatch (f, false)) else ()
          in
          let defn_opt =
            (match (elem1.felem_defn, elem2.felem_defn) with
             | (Some d1, None) -> Some d1
             | (None, Some d2) -> Some d2
             | (Some d1, Some d2) ->
                let _ = if not (check_equal_field_term loc fctx d1 d2) then
                          raise loc (FieldMismatch (f, true)) else ()
                in
                Some d1
             | (None, None) -> None)
          in
          let _ = if elem1.felem_is_ghost <> elem2.felem_is_ghost then
                    raise loc (Failure ("merge_global_fctxs: merging ghost and non-ghost fields for field name " ^ Id.to_string f))
                  else () in
          { felem_id = f; felem_is_ghost = elem1.felem_is_ghost;
            felem_type = elem1.felem_type; felem_defn = defn_opt }
       | (None, None) ->
          (* This should never happen! *)
          raise dummy_loc (Failure "merge_fctxs")
     in
     new_elem :: fctx)
    sorted_names_and_deps []


(* The types (if flag = false) or the definitions (if flag = true) of two
   fields, which are mapped to the same field by a substitution, are unequal *)
exception FieldOverlapMismatch of Id.t * Id.t * bool

(* Apply a substitution to an fctx element *)
let subst_fctx_elem loc fctx (subst:field_subst) elem =
  let (new_id, defn_opt) = subst_id subst elem.felem_id in
  let new_defn_opt =
    match (elem.felem_defn, defn_opt) with
    | (None, _) -> defn_opt
    | (Some defn, None) -> Some (subst_field_term subst defn)
    | (Some defn, Some defn') ->
       if check_equal_field_term loc fctx (subst_field_term subst defn) defn'
       then (Some defn')
       else raise loc (FieldAlreadyDefined elem.felem_id)
  in
  { elem with felem_id = new_id;
              felem_type = subst_field_term subst elem.felem_type;
              felem_defn = new_defn_opt }

(* Apply an fctx substitution to an fctx, raising a FieldOverlapMismatch if two
fields with distinct types or definitions are mapped to the same field *)
(* FIXME HERE: handle the fact that defns could require topo sorting... *)
(* FIXME HERE: make sure the subst domain includes the whole input context... *)
(* FIXME HERE: move these helper functions into the fctx section *)
let subst_fctx loc (subst:field_subst) (fctx:fctx) : fctx =
  (* For each fctx element elem satisfying pred, find the first element elem'
     which comes logically earlier in fctx (which means stored later in the list
     elems, because fctxs are stored backwards) that is mapped to the same field
     name by subst and also satisfies pred, if any. *)
  let rec mk_overlap_alist pred elems =
    match elems with
    | [] -> []
    | elem :: elems' ->
      if pred elem then
        (try (elem.felem_id,
              (List.find (fun elem' ->
                          pred elem' &&
                          Id.equal (fst (subst_id subst elem.felem_id))
                                   (fst (subst_id subst elem'.felem_id)))
                         elems').felem_id) :: mk_overlap_alist pred elems'
         with
           | Not_found -> mk_overlap_alist pred elems')
      else mk_overlap_alist pred elems'
  in
  (* Build overlap lists for error reporting, so that, if a type or definition
  mismatch occurs, we can say which two ops in the original fctx conflict. *)
  let tp_overlap_alist = mk_overlap_alist (fun _ -> true) fctx in
  let defn_overlap_alist = mk_overlap_alist (fun elem -> elem.felem_defn <> None) fctx in
  let overlap_lookup is_defn id_from =
    snd (List.find (fun p -> Id.equal id_from (fst p))
                   (if is_defn then defn_overlap_alist
                    else tp_overlap_alist))
  in
  let raise_overlap_error id_from is_defn =
         raise loc (FieldOverlapMismatch
                      (id_from, overlap_lookup is_defn id_from, is_defn))
  in
  (* Helper function to add a definition to an fctx elem *)
  let add_fctx_elem_defn fctx elem id_from id_to defn =
    match elem.felem_defn with
    | None -> { elem with felem_defn = Some defn }
    | Some defn' ->
       if check_equal_field_term loc fctx defn defn' then elem else
         raise_overlap_error id_from true
  in
  (* Helper function to add a definition to an fctx *)
  let rec add_fctx_defn fctx id_from id_to defn =
    match fctx with
    | [] -> raise loc (Failure "subst_fctx") (* Should not happen! *)
    | elem :: fctx' ->
      if Id.equal elem.felem_id id_to then
        add_fctx_elem_defn fctx' elem id_from id_to defn :: fctx'
      else
        elem :: add_fctx_defn fctx' id_from id_to defn
  in
  (* Now build up the out fctx, using the overlap lists to report any errors *)
  List.fold_right
    (fun elem fctx_out ->
     let elem_out = subst_fctx_elem loc fctx_out subst elem in
     match fctx_lookup fctx_out elem_out.felem_id with
     | None -> elem_out :: fctx_out
     | Some elem' ->
        let _ =
          if check_equal_field_term loc fctx_out elem.felem_type elem'.felem_type
          then ()
          else raise_overlap_error elem.felem_id false
        in
        (match elem.felem_defn with
         | None -> fctx_out
         | Some defn ->
            add_fctx_defn fctx_out elem.felem_id elem_out.felem_id defn)
    ) fctx []


(***
 *** The internal representation of specs
 ***)

(* A spec is represented internally as having two field contexts, one for ops
   and types (called just the "op context") and one for axioms and theorems
   (called the "axiom context"). The latter can depend on the former, but not
   vice-versa. *)
type spec = {
  spec_op_ctx : fctx;
  spec_axiom_ctx : fctx;
  spec_axiom_class_id : Id.t option
}

(* The empty local_spec *)
let empty_named_spec spec_id =
  { spec_op_ctx = []; spec_axiom_ctx = []; spec_axiom_class_id = Some spec_id }

(* The number of fields in a spec (mostly for debugging purposes) *)
(* FIXME: remove this *)
let spec_length spec =
  List.length (spec.spec_op_ctx @ spec.spec_axiom_ctx)

(* Get the full fctx of a spec, including the axiom and op contexts but only
including ghost fields if ghosts_p is true. Remember that fctxs are stored
backwards, so the axiom context, which depends on the op context, is listed
first. *)
let spec_full_fctx ghosts_p spec =
  let fctx = spec.spec_axiom_ctx @ spec.spec_axiom_ctx in
  if ghosts_p then fctx else fctx_non_ghosts fctx

(* Get the ids of all the non-defined axioms *)
let spec_axiom_ids spec =
  filter_map (fun elem -> if fctx_elem_has_def elem then None
                          else Some elem.felem_id)
             spec.spec_axiom_ctx

(* Two specs were merged where the given field is an op in one spec and an axiom
in the other *)
exception OpAxiomMismatch of Id.t

(* Merge two specs by merging their op and axiom contexts *)
let merge_specs loc spec1 spec2 =
  (* Check for overlap between op and axiom contexts *)
  let _ = fctx_iter_shared_fields
            (fun id -> raise loc (OpAxiomMismatch id))
            spec1.spec_op_ctx spec2.spec_axiom_ctx in
  let _ = fctx_iter_shared_fields
            (fun id -> raise loc (OpAxiomMismatch id))
            spec2.spec_op_ctx spec1.spec_axiom_ctx in
  {spec_op_ctx = merge_fctxs loc spec1.spec_op_ctx spec2.spec_op_ctx;
   spec_axiom_ctx = merge_fctxs loc spec1.spec_axiom_ctx spec2.spec_axiom_ctx;
   spec_axiom_class_id = None}

(* A substitution into a spec would map an op and an axiom to the same name *)
exception OpAxiomOverlap of Id.t * Id.t

(* Apply a substitution to a spec *)
let subst_spec loc subst spec =
  let spec_ret = {spec_op_ctx = subst_fctx loc subst spec.spec_op_ctx;
                  spec_axiom_ctx = subst_fctx loc subst spec.spec_axiom_ctx;
                  spec_axiom_class_id = None} in
  (* Check for overlap between op and axiom contexts in output spec *)
  let _ = fctx_iter_shared_fields
            (fun id ->
             let op_elem =
               List.find (fun elem ->
                          Id.equal (fst (subst_id subst elem.felem_id)) id)
                         spec.spec_op_ctx in
             let axiom_elem =
               List.find (fun elem ->
                          Id.equal (fst (subst_id subst elem.felem_id)) id)
                         spec.spec_axiom_ctx in
             raise loc (OpAxiomOverlap (op_elem.felem_id, axiom_elem.felem_id)))
            spec_ret.spec_op_ctx spec_ret.spec_axiom_ctx in
  spec_ret


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
     if Id.equal id_from id then Some id_to else
       translate_id xlate' id
  | NameXPrefix (pre_from, pre_to) :: xlate' ->
     (match match_prefix id pre_from with
      | Some id_suffix ->
         Some (Id.of_string (pre_to ^ id_suffix))
      | None -> translate_id xlate' id)

(* Resolve a name translation into a name substitution for a spec; if
   the total flag is set, make the returned substitution be total on
   all fields of spec (even if it is the identity on some of them) *)
let resolve_name_translation ?(total=false) spec xlate =
  concat_map (fun elem ->
              let id = elem.felem_id in
              let mapped_id =
                match translate_id xlate id with
                | None -> if total then Some id else None
                | Some id' -> Some id'
              in
              match mapped_id with
              | Some id' ->
                 (*
                 let _ = Format.eprintf "resolve_name_translation: mapped field %s to %s\n"
                                        (Id.to_string id) (Id.to_string id') in
                  *)
                 if fctx_elem_has_def elem then
                   (* If id is a def, also map id__eq -> id'__eq *)
                   [(id, id', None); (add_suffix id "eq", add_suffix id' "eq", None)]
                 else
                   [(id, id', None)]
              | None -> [])
             spec.spec_op_ctx
  @ filter_map (fun elem ->
                let id = elem.felem_id in
                match translate_id xlate id with
                | Some id' ->
                   (* Filter out mappings on "__eq" axioms *)
                   if has_suffix id "__eq" then None else
                     Some (id, id', None)
                | None -> None)
               spec.spec_axiom_ctx


(***
 *** Potential Morphisms
 ***)

(* A potential morphism is intuitively a morphism that does not yet have a
target spec. It thus also does not have any typeclass instances defined yet, and
so contains just a source spec (referred to by name) and a substitution. *)
type potential_morphism = spec_globref * spec * field_subst

(* Build the identity potential morphism *)
let make_id_pot_morphism spec spec_globref : potential_morphism =
  (spec_globref, spec,
   mk_id_subst (List.map (fun elem -> elem.felem_id)
                         (spec_full_fctx true spec)))

(* Substitute into a potential morphism *)
let subst_potential_morphism subst pot_m =
  let (globref, spec, subst') = pot_m in
  (globref, spec, compose_substs subst subst')

(* An instance map maps fields in some other spec to instances of those fields
in the current spec *)
type instance_map = Id.t Id.Map.t

(* The empty instance map *)
let instance_map_empty = Id.Map.empty

(* Apply a field in a global spec to the instances in an instance map *)
let apply_field_to_inst_map loc globref id arg_fields inst_map =
  try
    mk_ref_app_named_args
      (Qualid (loc, field_in_global_spec globref id))
      (List.map (fun id ->
                 (id, mk_var (loc, Id.Map.find id inst_map))) arg_fields)
  with Not_found ->
    raise loc (Failure "apply_field_to_inst_map")

(* Fresh names for generating instance names *)
let inst_name_counter = ref 0
let get_fresh_inst_name id =
  let i = !inst_name_counter in
  let _ = inst_name_counter := i + 1 in
  Id.of_string (Id.to_string id ^ "__inst__" ^ string_of_int i)

(* Create a typeclass instance of id_from in spec and add it to inst_map *)
let instance_map_add loc fctx globref spec (id_from, id_to, _) inst_map =
  let elem_from =
    match fctx_lookup (spec_full_fctx true spec) id_from with
    | None -> raise loc (Failure "instance_map_add")
    | Some elem -> elem
  in
  let from_fields = field_term_top_free_fields elem_from.felem_type in
  let tp = apply_field_to_inst_map loc globref (field_class_id id_from)
                                   from_fields inst_map in
  let inst_id = get_fresh_inst_name id_from in
  let _ = add_local_op_instance loc fctx (Name inst_id) tp (mk_var (loc, id_to)) in
  Id.Map.add id_from inst_id inst_map

(* Add instances for all the fields of the domain of a potential morphism,
returning an instance map for those fields *)
let add_potential_morphism_field_instances loc fctx (pot_m : potential_morphism) =
  let (globref, spec, subst) = pot_m in
  List.fold_right (instance_map_add loc fctx globref spec)
                  subst instance_map_empty

(* Add instances for all the fields and the axiom typeclass of the domain of a
potential morphism *)
let add_potential_morphism_instances loc fctx (pot_m : potential_morphism) =
  let inst_map = add_potential_morphism_field_instances loc fctx pot_m in
  let (globref, spec, subst) = pot_m in
  let axiom_class_id = match spec.spec_axiom_class_id with
    | Some id -> id
    | None -> raise loc (Failure "add_potential_morphism_instances")
  in
  let axiom_ids = spec_axiom_ids spec in
  add_local_record_instance
    loc fctx (Name (get_fresh_inst_name axiom_class_id))
    (apply_field_to_inst_map loc globref axiom_class_id axiom_ids inst_map)
    (List.map (fun id -> (id, mk_var (loc, Id.Map.find id inst_map))) axiom_ids)


(***
 *** Spec Morphisms
 ***)

(* A morphism is intuitively a substitution that maps from a source spec to a
target spec. Associated with this mapping is a set of typeclass instances, in
the context of the co-domain / target spec, of all of the typeclasses associated
with the domain / source spec; these include one instance for every op in the
source spec, and a single instance for all the axioms in the source spec. *)
type morphism = {
  morph_source : spec; (* FIXME: remove source and target specs in favor of refs *)
  morph_source_ref : spec_globref;
  morph_target : spec;
  morph_target_ref : spec_globref;
  morph_subst : field_subst;
  morph_op_insts : instance_map;
  morph_axiom_inst : constant
}

(* The variable name for the implicit spec argument of a morphism instance *)
let morph_spec_arg_id = Id.of_string "Spec"

(* Global table of named morphisms, indexed by the axiom typeclass instance *)
let morphism_table = ref (Cmap.empty)

(* Register a morphism in the morphism table *)
let register_morphism morph =
  morphism_table := Cmap.add morph.morph_axiom_inst morph !morphism_table

(* Indicates that a morphism was not found *)
exception MorphismNotFound of qualid

(* Look up a morphism by reference, raising Not_found if it does not exist *)
let lookup_morphism r =
  let loc = loc_of_reference r in
  let qualid = located_elem (qualid_of_reference r) in
  try
    let c = lookup_constant loc qualid in
    Cmap.find c !morphism_table
  with Not_found ->
    raise loc (MorphismNotFound qualid)

(* Apply a morphism to a spec. This is accomplished by: merging the spec with
the source of the morphism, which checks that all the types and definitions in
the spec agree with the morphism; applying the substitution of the morphism; and
then merging the target spec with the result, to add any additional fields not
in the range of the substitution. *)
let apply_morphism loc morph spec =
  let spec_in = merge_specs loc spec morph.morph_source in
  let spec_subst = subst_spec loc morph.morph_subst spec_in in
  merge_specs loc spec_subst morph.morph_target


(* FIXME HERE: update the following code ... *)

(* FIXME HERE: use spec_defn_term_local (which should actually be
   called "global" since it interprets the term outside of a spec) for
   the types of the parameters *)
(* Define a named morphism from the from spec to the to spec, both
   given by reference, via the given name translation *)
let start_morphism morph_name from_ref to_ref xlate =
  raise dummy_loc (Failure "start_morphism not yet implemented")

(*
  let loc = located_loc morph_name in
  let from_qualid = located_elem (qualid_of_reference from_ref) in
  let to_qualid = located_elem (qualid_of_reference to_ref) in
  let from_spec = lookup_spec from_qualid in
  let to_spec = lookup_spec to_qualid in
  let subst = resolve_name_translation ~total:true from_spec xlate in
  let finish_hook gr =
    register_morphism
      { morph_source = from_spec;
        morph_target = to_spec;
        morph_subst = subst;
        morph_interp = match gr with
                       | ConstRef c -> c
                       | _ -> anomaly (str "Morphism not a constant") } in
  ignore
    (Classes.new_instance
       false (* (fctx_params to_spec.spec_op_ctx @
                [mk_implicit_assum morph_spec_arg_id
                                   (mk_ref_app_named_args
                                      (spec_typeclass_ref loc to_qualid) [])]) *) []
       (lname_of_lident morph_name, Explicit,
        (mk_ref_app_named_args (spec_typeclass_ref loc from_qualid)
                               (subst_to_args subst)))
       None
       ~hook:finish_hook
       None)
 *)

(***
 *** Building up the current spec
 ***)

(* The currrent spec being defined, if one exists, along with its
   local name *)
let current_spec : spec option ref = ref None

(* There is no current spec *)
exception NoCurrentSpec

(* There is already a current spec *)
exception IsCurrentSpec

(* Incorrect name for the current spec *)
exception WrongCurrentSpecName

(* Get the current spec or throw an exception *)
let get_current_spec loc =
  match !current_spec with
  | Some spec -> spec
  | None -> raise loc NoCurrentSpec

(* Update the current spec, if it exists, by applying f *)
let update_current_spec loc f =
  match !current_spec with
  | Some spec ->
     current_spec := Some (f spec)
  | None -> raise loc NoCurrentSpec

(* The op_ctx of the current spec *)
let current_op_ctx loc =
  (get_current_spec loc).spec_op_ctx

(* The op_ctx and the axiom ctx of the current spec *)
let current_full_ctx loc =
  spec_full_fctx true (get_current_spec loc)

(* The op parameters in the current spec *)
let current_op_params loc =
  fctx_params loc (current_op_ctx loc)

(* All the parameters in the current spec *)
let current_all_params loc =
  fctx_params loc (current_full_ctx loc)

(* FIXME: error checks (e.g., name clashes with other ops / axioms) *)

(* Add a declared op to the current spec, creating a type-class for it *)
let add_declared_op op_name op_type =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let _ = Format.eprintf "\nadd_declared_op: %s of type %a in context %s\n"
                         (Id.to_string op_id) pp_constr_expr op_type
                         (fctx_to_string (current_op_ctx loc))
  in

  (* Add a type-class op_name__class : Type := op_name : op_type *)
  let tp_defn =
    add_local_op_typeclass loc (current_op_ctx loc) op_id false op_type
  in

  update_current_spec
    loc
    (fun s ->
     { s with
       spec_op_ctx =
         fctx_cons op_id false tp_defn None s.spec_op_ctx })

(* Add an axiom to the current spec, creating a definition for its type *)
let add_axiom ax_name is_ghost ax_type =
  let ax_id = located_elem ax_name in
  let loc = located_loc ax_name in
  let _ = Format.eprintf "\nadd_axiom: %s\n" (Id.to_string ax_id) in
  (* Add a type-class ax_name__class : Prop := ax_name : ax_type *)
  let tp_defn =
    add_local_op_typeclass loc (current_op_ctx loc) ax_id true ax_type
  in
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axiom_ctx = fctx_cons ax_id is_ghost tp_defn None s.spec_axiom_ctx })

(* FIXME HERE: make sure this is right: use typeclasses? *)
let add_defined_theorem thm_name thm_type thm_body =
  let thm_id = located_elem thm_name in
  let loc = located_loc thm_name in
  let tp_defn = add_local_op_typeclass loc (current_op_ctx loc)
                                       thm_id true thm_type
  in
  let def_defn =
    add_local_definition loc (current_full_ctx loc) thm_id
                         (Some (mk_var (loc, field_type_id thm_id))) thm_body
  in
  update_current_spec
    loc
    (fun s ->
     { s with
       spec_axiom_ctx = fctx_cons thm_id false tp_defn
                                  (Some def_defn) s.spec_axiom_ctx })

(* Add a defined op to the current spec, creating a type-class and def for it *)
let add_defined_op op_name op_type_opt op_body =
  let op_id = located_elem op_name in
  let loc = located_loc op_name in
  let op_type =
    match op_type_opt with
    | Some op_type -> op_type
    | None -> CHole (loc, None, IntroIdentifier op_id, None)
  in
  let op_ctx = current_op_ctx loc in
  let op_var_id = add_suffix_l op_name "var" in
  let _ = Format.eprintf "\nadd_defined_op: %s\n" (Id.to_string op_id) in

  (* Add a definition op_name : op_type := op_body *)
  let def_defn = add_local_definition loc op_ctx op_id (Some op_type) op_body in

  (* Add a type-class for op_name__class : Type := op_name__var : op_type *)
  let tp_defn =
    add_local_op_typeclass loc op_ctx op_id false op_type in

  (* Add the new op to spec *)
  let _ =
    update_current_spec
      loc
      (fun s ->
       { s with
         spec_op_ctx =
           fctx_cons op_id false tp_defn (Some def_defn) s.spec_op_ctx }) in

  (* Add an axiom "op_name = op_name__var" to the resulting spec *)
  add_axiom
    (add_suffix_l op_name "eq") true
    (mk_ident_equality op_var_id op_name)

(* Complete the current spec, by creating its axiom type-class and
   registering it in the global spec table. No more axioms can be
   added to a spec once it has been completed. Return the globalized
   version of the current spec. *)
let complete_spec loc =
  match !current_spec with
  | None -> raise loc NoCurrentSpec
  | Some spec ->
     let class_id = match spec.spec_axiom_class_id with
       | Some id -> id
       | None -> raise loc (Failure "complete_spec")
     in
     let ax_fields =
       List.rev_map
         (fun elem -> ((loc, field_axelem_id elem.felem_id),
                       mk_var (loc, field_class_id elem.felem_id),
                       true))
         (List.filter (fun elem -> elem.felem_defn = None) spec.spec_axiom_ctx)
     in
     let _ = add_typeclass (loc, class_id) false true
                           (current_op_params loc) ax_fields in
     let spec_globref = global_modpath (Nametab.locate (qualid_of_ident class_id)) in
     let _ = register_spec spec_globref spec in
     spec

(* Start the interactive definition of a new spec *)
let begin_new_spec spec_lid =
  if !current_spec = None then
    (current_spec := Some (empty_named_spec (located_elem spec_lid));
     begin_module spec_lid)
  else
    raise (located_loc spec_lid) IsCurrentSpec

(* Finish the interactive definition of a new spec by completing it
   and clearing current_spec; return the newly defined spec *)
let end_new_spec lid =
  let loc = located_loc lid in
  match !current_spec with
  | Some spec ->
     let class_id = match spec.spec_axiom_class_id with
       | Some id -> id
       | None -> raise loc (Failure "complete_spec")
     in
     if Id.equal class_id (located_elem lid) then
       let spec = complete_spec loc in
       let _ = end_module lid in
       let _ = current_spec := None in
       spec
     else
       raise loc WrongCurrentSpecName
  | None -> raise loc NoCurrentSpec

(* Build a new spec in a new module called spec_id, calling builder
   inside that new module to build the spec. Builder should not
   complete or globalize the spec. Unlike begin_new_spec,
   within_named_spec can be nested inside another spec definition *)
let within_named_spec spec_lid builder =
  let spec_id = located_elem spec_lid in
  let loc = located_loc spec_lid in
  let saved_spec = !current_spec in
  let _ = current_spec := Some (empty_named_spec spec_id) in
  let spec = within_module spec_lid
                           (fun () -> builder (); complete_spec loc) in
  let _ = current_spec := saved_spec in
  spec


(***
 *** Spec Terms and Imports
 ***)

(* Spec terms are syntactic forms for building specs from existing
   specs *)
type spec_term =
  (* A reference by name to an existing spec *)
  | SpecRef of reference
  (* A translation of the names of a spec *)
  | SpecXlate of spec_term * Loc.t * name_translation
  (* A spec substitution, where the morphism must be named *)
  | SpecSubst of spec_term * reference
  (* Adding definitions to ops in a spec *)
  | SpecAddDefs of spec_term * Loc.t * (lident * Constrexpr.constr_expr) list

(* Interpret a spec term into a spec plus a list of potential morphisms to the
returned spec. The spec term is not allowed to add definitions. *)
let rec interp_spec_term sterm : spec * potential_morphism list =
  match sterm with
  | SpecRef r ->
     (try
         let locref = spec_locref_of_ref r in
         let (spec, globref) = lookup_spec_and_globref locref in
         (spec, [make_id_pot_morphism spec globref])
       with Not_found ->
         user_err_loc (loc_of_reference r, "_",
                       str ("No spec named " ^ string_of_reference r)))
  | SpecXlate (sterm', loc, xlate) ->
     let (spec, insts) = interp_spec_term sterm' in
     let subst = resolve_name_translation spec xlate in
     (*
     let _ =
       List.iter (fun (id_from, id_to) ->
                   Format.eprintf "Translating %s to %s\n"
                                  (Id.to_string id_from)
                                  (Id.to_string id_to)) subst in
      *)
     (subst_spec loc subst spec,
      List.map (subst_potential_morphism subst) insts)
  | SpecSubst (sterm', morph_ref) ->
     (try
         let (spec, insts) = interp_spec_term sterm' in
         let loc = loc_of_reference morph_ref in
         let morph = lookup_morphism morph_ref in
         (apply_morphism loc morph spec,
          make_id_pot_morphism morph.morph_target morph.morph_target_ref ::
            List.map (subst_potential_morphism morph.morph_subst) insts)
       with Not_found ->
         user_err_loc (loc_of_reference morph_ref, "_",
                       str ("No morphism named " ^ string_of_reference morph_ref)))
  | SpecAddDefs (sterm', loc, defs) ->
     let (spec, insts) = interp_spec_term sterm' in
     let subst =
       make_subst_for_defs defs
                           (List.map (fun ((_, id), d) ->
                                      (id, mk_fctx_term spec.spec_op_ctx d))
                                     defs)
     in
     (subst_spec loc subst spec,
      List.map (subst_potential_morphism subst) insts)

(* Add an fctx_elem to the current spec *)
(* FIXME HERE NOW: test if the element already exists *)
let import_fctx_elem loc is_axiom elem =
  if elem.felem_is_ghost then () else
    match (is_axiom, elem.felem_defn) with
    | (true, None) ->
       add_axiom (loc, elem.felem_id) false
                 (field_term_to_expr elem.felem_type)
    | (true, Some defn) ->
       add_defined_theorem (loc, elem.felem_id)
                           (field_term_to_expr elem.felem_type)
                           (field_term_to_expr defn)
    | (false, None) ->
       add_declared_op (loc, elem.felem_id) (field_term_to_expr elem.felem_type)
    | (false, Some defn) ->
       add_defined_op (loc, elem.felem_id)
                      (Some (field_term_to_expr elem.felem_type))
                      (field_term_to_expr defn)

(* Import a spec term into the current spec *)
let import_spec_term loc sterm =
  let (spec, insts) = interp_spec_term sterm in
  let _ =
    List.iter (import_fctx_elem loc false) (List.rev spec.spec_op_ctx)
  in
  let _ =
    List.iter (import_fctx_elem loc true) (List.rev spec.spec_axiom_ctx)
  in
  List.iter (add_potential_morphism_instances loc (current_full_ctx loc)) insts


(***
 *** Additions to the Coq parser
 ***)

(* Run f, catching any exceptions and turning them into user_errors *)
(* FIXME: actually write this! *)
let reporting_exceptions f =
  f ()

(* FIXME: get the locations of all the identifiers right! *)

(* Syntactic class to parse name translation elements *)
VERNAC ARGUMENT EXTEND name_translation_elem
  | [ ident(lhs) "+->" ident(rhs) ] -> [ NameXSingle (lhs,rhs) ]
  | [ ident(lhs) "%" "+->" ident(rhs) "%" ] ->
     [ NameXPrefix (Id.to_string lhs, Id.to_string rhs) ]
END

(* Syntactic class to parse name translations *)
VERNAC ARGUMENT EXTEND name_translation
  | [ name_translation_elem(elem) ";" name_translation (rest) ] -> [ elem::rest ]
  | [ name_translation_elem(elem) ] -> [ [elem] ]
END

(* Syntactic class to parse spec term defs *)
type spec_term_defs = (lident * Constrexpr.constr_expr) list
VERNAC ARGUMENT EXTEND spec_term_defs
  | [ ident(id) ":=" constr(def) ";" spec_term_defs(rest) ] -> [ ((dummy_loc,id), def)::rest ]
  | [ ident(id) ":=" constr(def) ] -> [ [(dummy_loc,id), def] ]
END

(* Syntactic class to parse spec terms *)
VERNAC ARGUMENT EXTEND spec_term
  | [ global(r) ] -> [ SpecRef r ]
  | [ spec_term(st) "{" name_translation(xlate) "}" ] -> [ SpecXlate (st, dummy_loc, xlate) ]
  | [ spec_term(st) "[" global(morph_ref) "]" ] -> [ SpecSubst (st, morph_ref) ]
  | [ spec_term(st) "with" spec_term_defs(defs) ] -> [ SpecAddDefs (st, dummy_loc, defs) ]
END

(* Top-level syntax for specs *)
VERNAC COMMAND EXTEND Spec
  (* Define a spec via a spec term *)
  | [ "Spec" ident(spec_name) ":=" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [spec_name], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () ->
            ignore
              (within_named_spec (dummy_loc, spec_name)
                                 (fun () -> import_spec_term dummy_loc st))) ]

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
           (fun () -> add_declared_op (dummy_loc,id) tp) ]

  (* Add a defined op with a type *)
  | [ "Spec" "Definition" ident(id) ":" constr(tp) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) (Some tp) body) ]
  (* Add a defined op without a type *)
  | [ "Spec" "Definition" ident(id) ":=" constr(body) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_defined_op (dummy_loc,id) None body) ]

  (* Add an axiom *)
  | [ "Spec" "Axiom" ident(id) ":" constr(tp) ]
    => [ (Vernacexpr.VtSideff [id], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> add_axiom (dummy_loc,id) false tp) ]

  (* Import a spec term *)
  | [ "Spec" "Import" spec_term(st) ]
    => [ (Vernacexpr.VtSideff [], Vernacexpr.VtLater) ]
    -> [ reporting_exceptions
           (fun () -> import_spec_term dummy_loc st) ]
END

(* Top-level syntax for morphisms *)
VERNAC COMMAND EXTEND Morphism
  (* Define a named morphism with the given name translation *)
  | [ "Spec" "Morphism" ident(spec_name) ":" global(s1) "->" global(s2)
             "{" name_translation(xlate) "}" ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity, [spec_name]),
          Vernacexpr.VtLater) ]
    -> [ start_morphism (dummy_loc, spec_name) s1 s2 xlate ]

  (* Define a named morphism with no name translation *)
  | [ "Spec" "Morphism" ident(spec_name) ":" global(s1) "->" global(s2) ]
    => [ (Vernacexpr.VtStartProof ("Classic", Doesn'tGuaranteeOpacity, [spec_name]),
          Vernacexpr.VtLater) ]
    -> [ start_morphism (dummy_loc, spec_name) s1 s2 [] ]
END
