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
 *** Debugging support
 ***)

let debug_level = ref 1

let debug_printf level args =
  if !debug_level >= level then
    Format.eprintf args
  else
    Format.ifprintf Format.std_formatter args


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

(* Same as filter_map, but also reverse the list *)
let rev_filter_map f l =
  let rec helper l acc =
    match l with
    | [] -> acc
    | x :: l' ->
       helper l' (match f x with
                  | Some y -> (y::acc)
                  | None -> acc)
  in helper l []

(* Map f on a list and concatenate the results *)
let concat_map f l =
  List.concat (List.map f l)

(* Topo sort failed because of a circularity *)
exception TopoCircularity of int

(* Stable topological sort: sort l so that every element x comes after (or
   before, if reverse_p is set) its dependencies, favoring the existing ordering
   of l where possible. The dependencies of x are all nodes y whose key, given
   by the key function, is key_eq to a key in (deps x). *)
(* FIXME: use sets for deps instead of lists *)
let rec stable_topo_sort ?(reverse_p=false) loc key key_eq deps l =
  let arr = Array.of_list l in
  let arr_deps = Array.make (List.length l) [] in
  let visited = Array.make (List.length l) false in
  let rec get_node_by_key_help k j =
    if j >= Array.length arr then None
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
             if List.mem j arr_deps.(i) then
               (if reverse_p then 1 else -1)
             else if List.mem i arr_deps.(j) then
               (if reverse_p then -1 else 1)
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

(* Pretty-print a type error *)
let pp_type_error env fmt e =
  Pp.pp_with fmt (Himsg.explain_type_error env Evd.empty e)

(* Pretty-print a pretyping error *)
let pp_pretype_error env evd fmt e =
  Pp.pp_with fmt (Himsg.explain_pretype_error env evd e)

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
let mk_ref_app_named_args loc r args =
  CApp (loc,
        (None, CRef (r, None)),
        List.map (fun (id,arg) ->
                  (arg, Some (dummy_loc, ExplByName id))) args)

(* Build an expression for a variable applied to named implicit args,
   where the args are given as (name,value) pairs *)
let mk_id_app_named_args loc id args =
  mk_ref_app_named_args loc (Ident id) args

(* Build a qualified id (NOTE: dir is *not* reversed here) *)
let mk_qualid dir id =
  make_qualid (DirPath.make (List.rev_map Id.of_string dir)) id

(* Cons an id onto the end of a qualid *)
let qualid_cons qualid id =
  let (mod_path,mod_name) = repr_qualid qualid in
  make_qualid (DirPath.make ([mod_name] @ DirPath.repr mod_path)) id

(* Build a term for a global constant, where dir lists the module path
   as a list (e.g., ["Coq"; "Init"; "Logic"]) and id is the id *)
let mk_reference dir name =
  CRef (Qualid (dummy_loc, mk_qualid dir (Id.of_string name)), None)

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
let qualid_of_global gr =
  Nametab.shortest_qualid_of_global Id.Set.empty gr

(* Build an expression for a global applied to named implicit args *)
let mk_global_app_named_args gr args =
  mk_ref_app_named_args dummy_loc (Qualid (dummy_loc, qualid_of_global gr)) args

(* Build an exprssion for a global with @ in front of it *)
let mk_global_expl gr =
  CAppExpl (dummy_loc,
            (None, (Qualid (dummy_loc, qualid_of_global gr)), None),
            [])

(* Look up a defined constant by path list and string name *)
let mk_constant loc dir name =
  let qualid = mk_qualid dir (Id.of_string name) in
  match Nametab.locate qualid with
  | ConstRef c -> c
  | _ -> user_err_loc (dummy_loc, "_",
                       str ("Not a constant: " ^ string_of_qualid qualid))

(* Look up a constructor by a path list and a string name *)
let mk_constructor loc dir name =
  let qualid = mk_qualid dir (Id.of_string name) in
  match Nametab.locate qualid with
  | ConstructRef c -> c
  | _ -> user_err_loc (dummy_loc, "_",
                       str ("Not a constructor: " ^ string_of_qualid qualid))

(* Look up an identifier in the current module and make it fully qualified *)
let qualify_identifier id =
  let _ = debug_printf 2 "@[qualify_identifier: %s@]\n" (Id.to_string id) in
  qualid_of_global (Nametab.locate (qualid_of_ident id))

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
  let cmd = VernacDefinition
              ((None, Definition), id,
               DefineBody (params, None, body, type_opt))
  in
  let _ = debug_printf 1 "@[add_definition command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc id, cmd)

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
  let _ = debug_printf 1 "@[add_typeclass command:@ %a@]\n" pp_vernac cmd in
  interp (located_loc class_id, cmd)

(* Add an instance of an typeclass that is a single term *)
let add_term_instance inst_name inst_params inst_tp inst_body =
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Decl_kinds.Explicit, inst_tp),
               Some (false, inst_body),
               None)
  in
  let _ = debug_printf 1 "@[add_term_instance command:@ %a@]\n" pp_vernac cmd in
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
  let _ = debug_printf 1 "@[add_record_instance command:@ %a@]\n" pp_vernac cmd in
  interp (loc, cmd)

(* Begin an interactively-defined instance *)
let begin_instance ?(hook=(fun _ -> ())) inst_params inst_name inst_tp =
  let cmd = VernacInstance
              (false, inst_params,
               (inst_name, Explicit, inst_tp),
               None, None)
  in
  let _ = debug_printf 1 "@[begin_instance command:@ %a@]\n" pp_vernac cmd in
  ignore
    (Classes.new_instance
       false inst_params (inst_name, Explicit, inst_tp) None ~hook:hook None)

(* Begin a new module *)
let begin_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacDefineModule (None, mod_name, [], Check [], []))

(* End the current module, which should have name mod_name *)
let end_module mod_name =
  let loc = located_loc mod_name in
  interp (loc, VernacEndSegment mod_name)

(* Begin a new section *)
let begin_section sect_id =
  Lib.open_section sect_id

(* End the current section *)
let end_section () =
  Lib.close_section ()

(* Perform some operation(s) inside a newly-defined module *)
let within_module mod_name f =
  let _ = begin_module mod_name in
  let ret = f () in
  let _ = end_module mod_name in
  ret

(* Reduce a constr using a list of reduction expressions *)
let reduce_constr reds constr =
  let env = Global.env () in
  let evdref = ref Evd.empty in
  let apply_redexpr c r =
    let (evd,r_interp) = Tacinterp.interp_redexp env !evdref r in
    let _ = evdref := evd in
    snd (fst (Redexpr.reduction_of_red_expr env r_interp) env !evdref c) in
  List.fold_left apply_redexpr constr reds

(* Reduce a constr to head normal form *)
let hnf_constr constr =
  reduce_constr [Hnf] constr

(* Reduce a constr using the "compute" reduction (which is call-by-value) *)
let compute_constr constr =
  reduce_constr
    [Cbv (Redops.make_red_flag [FBeta;FIota;FZeta;FDeltaBut []])]
    constr

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
                debug_printf "\nunfold_fold_term: unfolding %s to %a"
                               (Id.to_string id)
                               pp_constr_expr (uninterp_term res_to) in
               *)
             (res_from, res_to)) folds in
  let constr_out = fold_constr_vars folds_c constr_unfolded in
  let res = uninterp_term constr_out in
  (*
  let _ = debug_printf "\nunfold_fold_term: unfolded term: %a\n" pp_constr_expr
                         (uninterp_term constr_unfolded) in
   *)
  let _ = debug_printf 2 "@[unfold_fold_term: returning@ %a@]\n"
                       pp_constr_expr res in
  res

(* Test if constr is a constant equal to const *)
let constr_is_constant const constr =
  match Term.kind_of_term constr with
  | Term.Const (c, _) -> Constant.equal c const
  | _ -> false

(* Test if constr is a constructor equal to ctor *)
let constr_is_constructor ctor constr =
  match Term.kind_of_term constr with
  | Term.Construct (c, _) -> eq_constructor c ctor
  | _ -> false

(* Build the expression t1 = t2 *)
let mk_equality t1 t2 =
  CApp (dummy_loc,
        (None, mk_reference ["Coq"; "Init"; "Logic"] "eq"),
        [(t1, None); (t2, None)])

(* Build the expression id1 = id2 for identifiers id1 and id2 *)
let mk_ident_equality id1 id2 =
  mk_equality (mk_var id1) (mk_var id2)

(* Build the expression t1::t2::...::tn::nil *)
(* FIXME: use build_constr_expr below *)
let mk_list loc ts =
  List.fold_right
    (fun t rest ->
     mkAppC (mk_reference ["Coq"; "Init"; "Datatypes"] "cons",
             [t; rest]))
    ts
    (mk_reference ["Coq"; "Init"; "Datatypes"] "nil")

(* Check that two terms are definitionally equal relative to the given
   parameter list, by checking that (forall params, eq_refl : t1=t2)
   is well-typed (eq_refl is the constructor for the equality type) *)
let check_equal_term params t1 t2 =
  let cmd = VernacCheckMayEval
              (None, None,
               (mkCLambdaN
                  dummy_loc
                  params
                  (CCast (dummy_loc,
                          CApp (dummy_loc,
                                (None, mk_reference
                                         ["Coq"; "Init"; "Logic"] "eq_refl"),
                                [(t1, None)]),
                          CastConv (mk_equality t1 t2)))))
  in
  let _ = debug_printf 2 "@[check_equal_term command:@ %a@]\n" pp_vernac cmd in
  try interp (dummy_loc, cmd); true
  with Type_errors.TypeError (env, err) ->
       let _ = debug_printf 1 "@[check_equal_term:@ %a@]\n" (pp_type_error env) err in
       false
     | Pretype_errors.PretypeError (env, evd, err) ->
       let _ = debug_printf 1 "@[check_equal_term:@ %a@]\n"
                            (pp_pretype_error env evd) err in
       false


(***
 *** Building and Destructing Coq Inductive Objects
 ***)

type empty = {elim_empty: 'a . 'a}

type ('a, 'b) sum =
  | Left of 'a
  | Right of 'b

(* Descriptions of the values of some Coq type, given as a "way" to map values
of the Coq type to and from some OCaml type: ('t,'f) constr_descr describes
how to destruct Coq values of this type to type 'to, and how to build Coq
expressions of this type from elements of type 'f. *)
type (_,_) constr_descr =
  | Descr_Ctor : constructor * (('t1,'f1) constr_array_descr) *
                   ('t2,'f2) constr_descr ->
                 (('t1,'t2) sum, ('f1,'f2) sum) constr_descr
  | Descr_Fail : (empty, empty) constr_descr
  | Descr_Constr : (Constr.t, constr_expr) constr_descr
  | Descr_Iso : ('t1 -> 't2) * ('f2 -> 'f1) *
                  ('t1, 'f1) constr_descr -> ('t2, 'f2) constr_descr
  | Descr_ConstrMap : (Constr.t -> Constr.t) *
                        (constr_expr -> constr_expr) *
                          ('t, 'f) constr_descr ->
                      ('t, 'f) constr_descr
  | Descr_Rec : (('t, 'f) constr_descr -> ('t, 'f) constr_descr) ->
                ('t, 'f) constr_descr
  | Descr_Direct : (Constr.t -> 't option) * ('f -> constr_expr) ->
                   ('t,'f) constr_descr
 and (_,_) constr_array_descr =
   | ArrayDescr_Nil : (unit,unit) constr_array_descr
   | ArrayDescr_Cons : ('t1,'f1) constr_descr *
                         (('t1,'f1) sum -> ('t2, 'f2) constr_array_descr) ->
                       ('t1 * 't2, 'f1 * 'f2) constr_array_descr
   | ArrayDescr_Direct : (Constr.t list -> 't option) *
                           ('f -> constr_expr list) -> ('t,'f) constr_array_descr

(* Build a constr_expr from a description *)
let rec build_constr_expr : type t f. (t,f) constr_descr -> f -> constr_expr = function
  | Descr_Ctor (ctor,array_descr,descr') ->
     (function
       | Left a -> mkAppC (mk_global_expl (ConstructRef ctor),
                           build_constr_expr_list array_descr a)
       | Right b -> build_constr_expr descr' b)
  | Descr_Fail -> fun emp -> emp.elim_empty
  | Descr_Constr -> fun constr_expr -> constr_expr
  | Descr_Iso (iso_to, iso_from, descr') ->
     fun b -> build_constr_expr descr' (iso_from b)
  | Descr_ConstrMap (map_to, map_from, descr') ->
     fun a -> map_from (build_constr_expr descr' a)
  | Descr_Rec f -> build_constr_expr (f (Descr_Rec f))
  | Descr_Direct (f_to,f_from) -> f_from
and build_constr_expr_list : type t f. (t,f) constr_array_descr -> f -> constr_expr list = function
  | ArrayDescr_Nil -> fun () -> []
  | ArrayDescr_Cons (descr, rest) ->
     fun (a,b) -> let constr = build_constr_expr descr a in
                  constr :: build_constr_expr_list (rest (Right a)) b
  | ArrayDescr_Direct (f_to,f_from) -> f_from

(* Destruct a constr using a description *)
let rec destruct_constr : type t f. (t,f) constr_descr -> Constr.t -> t option = function
  | Descr_Ctor (ctor,array_descr,descr') ->
     fun constr ->
     let head_args_opt =
       match Term.kind_of_term constr with
       | Term.App (f, args) ->
          (match Term.kind_of_term f with
           | Term.Construct (c, _) -> Some (c, args)
           | _ -> None)
       | Term.Construct (c, _) -> Some (c, [| |])
       | _ -> None
     in
     (match head_args_opt with
      | Some (c, args) ->
         if eq_constructor c ctor then
           map_opt (fun x -> Left x) (destruct_constr_array array_descr args)
         else
           map_opt (fun x -> Right x) (destruct_constr descr' constr)
      | None -> None)
  | Descr_Fail -> fun constr -> None
  | Descr_Constr -> fun constr -> Some constr
  | Descr_Iso (iso_to, iso_from, descr') ->
     fun constr -> map_opt iso_to (destruct_constr descr' constr)
  | Descr_ConstrMap (map_to, map_from, descr') ->
     fun constr -> destruct_constr descr' (map_to constr)
  | Descr_Rec f -> destruct_constr (f (Descr_Rec f))
  | Descr_Direct (f_to,f_from) -> f_to
and destruct_constr_list : type t f. (t,f) constr_array_descr -> Constr.t list -> t option = function
  | ArrayDescr_Nil -> (function [] -> Some () | _ -> None)
  | ArrayDescr_Cons (descr, rest) ->
     (function
       | [] -> None
       | constr::constrs ->
          match destruct_constr descr constr with
          | Some a -> map_opt (fun b -> (a,b))
                              (destruct_constr_list (rest (Left a)) constrs)
          | None -> None)
  | ArrayDescr_Direct (f_to,f_from) -> f_to
and destruct_constr_array : type t f. (t,f) constr_array_descr -> Constr.t array -> t option =
  fun descr constrs -> destruct_constr_list descr (Array.to_list constrs)

(* Helpers for building descriptions *)
let nullary_ctor : 't_rest 'f_rest . string list -> string -> ('t_rest,'f_rest) constr_descr ->
                   ((unit, 't_rest) sum, (unit, 'f_rest) sum) constr_descr =
  fun dir name descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Nil, descr_rest)
let unary_ctor : 't1 'f1 't_rest 'f_rest . string list -> string ->
                 ('t1,'f1) constr_descr ->
                 ('t_rest,'f_rest) constr_descr ->
                 (('t1 * unit, 't_rest) sum,
                  ('f1 * unit, 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons (descr_a, fun _ -> ArrayDescr_Nil), descr_rest)
let binary_ctor : 't1 'f1 't2 'f2 't_rest 'f_rest . string list -> string ->
                  ('t1,'f1) constr_descr ->
                  (('t1,'f1) sum -> ('t2,'f2) constr_descr) ->
                  ('t_rest,'f_rest) constr_descr ->
                  (('t1 * ('t2 * unit), 't_rest) sum,
                   ('f1 * ('f2 * unit), 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_b descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons (descr_b a, fun _ -> ArrayDescr_Nil)),
              descr_rest)
let ternary_ctor : 't1 'f1 't2 'f2 't3 'f3 't_rest 'f_rest .
                   string list -> string ->
                   ('t1,'f1) constr_descr ->
                   (('t1,'f1) sum -> ('t2,'f2) constr_descr) ->
                   (('t1,'f1) sum -> ('t2,'f2) sum -> ('t3,'f3) constr_descr) ->
                   ('t_rest,'f_rest) constr_descr ->
                   (('t1 * ('t2 * ('t3 * unit)), 't_rest) sum,
                    ('f1 * ('f2 * ('f3 * unit)), 'f_rest) sum) constr_descr =
  fun dir name descr_a descr_b descr_c descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons
                   (descr_b a,
                    fun b -> ArrayDescr_Cons
                               (descr_c a b, fun _ -> ArrayDescr_Nil))),
              descr_rest)
let quaternary_ctor =
  fun dir name descr_a descr_b descr_c descr_d descr_rest ->
  Descr_Ctor (mk_constructor dummy_loc dir name,
              ArrayDescr_Cons
                (descr_a,
                 fun a ->
                 ArrayDescr_Cons
                   (descr_b a,
                    fun b ->
                    ArrayDescr_Cons
                      (descr_c a b,
                       fun c ->
                       ArrayDescr_Cons
                         (descr_d a b c, fun _ -> ArrayDescr_Nil)))),
              descr_rest)

(* Description that always builds a hole *)
let hole_descr : (Constr.t, unit) constr_descr =
  Descr_Iso ((fun x -> x),
             (fun () -> CHole (dummy_loc, None, IntroAnonymous, None)),
             Descr_Constr)

(* The module for many Coq datatypes *)
let datatypes_mod = ["Coq"; "Init"; "Datatypes"]

(* Description of the Coq Boolean type *)
let bool_descr : (bool,bool) constr_descr =
  Descr_Iso ((function
               | Left () -> true
               | Right (Left ()) -> false
               | Right (Right emp) -> emp.elim_empty),
             (fun b -> if b then Left () else Right (Left ())),
             (nullary_ctor datatypes_mod "true"
                           (nullary_ctor datatypes_mod "false" Descr_Fail)))

(* Description of the Coq pair type *)
let pair_descr (descr1 : ('t1,'f1) constr_descr)
               (descr2 : ('t2,'f2) constr_descr) :
      ('t1 * 't2, 'f1 * 'f2) constr_descr =
  Descr_Iso ((function
               | Left (tpa_ctor, (tpb_ctor, (a, (b, ())))) -> (a, b)
               | Right emp -> emp.elim_empty),
             (fun (a,b) -> Left ((), ((), (a, (b, ()))))),
             quaternary_ctor
               datatypes_mod "pair" hole_descr (fun _ -> hole_descr)
               (fun _ _ -> descr1) (fun _ _ _ -> descr2) Descr_Fail
            )

(* Description of the Coq option type *)
let option_descr (descr : ('t,'f) constr_descr) :
      ('t option, 'f option) constr_descr =
  Descr_Iso ((function
               | Left (tp, (x, ())) -> Some x
               | Right (Left (tp, ())) -> None
               | Right (Right emp) -> emp.elim_empty),
             (function
               | Some x -> Left ((), (x, ()))
               | None -> Right (Left ((), ()))),
             binary_ctor
               datatypes_mod "Some" hole_descr (fun _ -> descr)
               (unary_ctor datatypes_mod "None" hole_descr Descr_Fail))

(* Description of the Coq list type *)
let list_descr (descr : ('t,'f) constr_descr) :
      ('t list, 'f list) constr_descr =
  Descr_Rec
    (fun l_descr ->
     Descr_Iso
       ((function
          | Left (tp, (x, (rest, ()))) -> x::rest
          | Right (Left (tp, ())) -> []
          | Right (Right emp) -> emp.elim_empty),
        (function
          | x::l -> Left ((), (x, (l, ())))
          | [] -> Right (Left ((), ()))),
        ternary_ctor
          datatypes_mod "cons" hole_descr (fun _ -> descr) (fun _ _ -> l_descr)
          (unary_ctor datatypes_mod "nil" hole_descr Descr_Fail)))

(* Decode a little-endian list of booleans into an int *)
let rec decode_ascii_bits bits =
  match bits with
  | [] -> 0
  | b :: bits' -> (if b then 1 else 0) + 2 * decode_ascii_bits bits'

(* Encode an int into a little-endian list of booleans of length n *)
let rec encode_ascii_bits n i =
  if n = 0 then [] else
    (i mod 2 > 0) :: encode_ascii_bits (n-1) (i/2)

(* Description of the Coq Ascii type *)
let ascii_descr : (char, char) constr_descr =
  Descr_Iso
    ((function
       | Left c -> c
       | Right emp -> emp.elim_empty),
     (fun c -> Left c),
     Descr_Ctor
       (mk_constructor dummy_loc ["Coq"; "Strings"; "Ascii"] "Ascii",
        (ArrayDescr_Direct
           ((fun args ->
             if List.length args = 8 then
               match
                 (List.fold_right
                    (fun bit_c bits_opt ->
                     match (destruct_constr bool_descr bit_c, bits_opt) with
                     | (Some b, Some bits) -> Some (b::bits)
                     | _ -> None)
                    args (Some []))
               with
               | Some bits -> Some (char_of_int (decode_ascii_bits bits))
               | None -> None
             else None),
            (fun c ->
             List.map (fun b ->
                       mk_reference datatypes_mod (if b then "true" else "false"))
                      (encode_ascii_bits 8 (int_of_char c))))
         : (char, char) constr_array_descr),
        Descr_Fail))

(* Description of the Coq string type *)
let string_descr : (string, string) constr_descr =
  Descr_Rec
    (fun str_descr ->
     Descr_Iso
       ((function
          | Left (c, (l, ())) -> (String.make 1 c)^l
          | Right (Left ()) -> String.make 0 'a'
          | Right (Right emp) -> emp.elim_empty),
        (fun str ->
         let len = String.length str in
         if len > 0 then
           Left (String.get str 0, (String.sub str 1 (len-1), ()))
         else
           Right (Left ())),
        binary_ctor
          ["Coq"; "Strings"; "String"] "String" ascii_descr (fun _ -> str_descr)
          (nullary_ctor ["Coq"; "Strings"; "String"] "EmptyString" Descr_Fail)))

(* An optimized description of the Coq string type, that converts strings
directly to string literals instead of cons-list expressions *)
let string_fast_descr : (string, string) constr_descr =
  Descr_Direct
    (destruct_constr string_descr,
     (fun str ->
      CDelimiters (dummy_loc, "string",
                   CPrim (dummy_loc, String str))))

let mk_string = build_constr_expr string_fast_descr