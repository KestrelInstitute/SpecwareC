(* Copyright (c) 2015, Kestrel Institute
All rights reserved.

This program is free software; you can redistribute it and/or modify it under
the terms of the included LICENSE.txt file.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the LICENSE.txt for more details. *)


Require Export Spec.

Declare ML Module "specware_c_plugin".


(*** We use this spec to define tactics that depend on the OCaml code ***)

(* Tactic to begin a refinement *)
Ltac start_refinement :=
  (raw_evar
     "__Spec"%string Spec
     (fun evar =>
        refine (Build_GMRefinement _ ?__Spec _)));
  intros __R __model __r;
  econstructor; constructor.


(* Tactics to instantiate a pushout *)

Ltac apply_spec_ctor_axioms_evars ctor axioms :=
  lazymatch axioms with
    | nil => apply ctor
    | cons (specAxiom ?f ?P) ?axioms' =>
      (raw_evar
         f P
         (fun evar =>
            let ctor' := constr:(ctor evar) in
            apply_spec_ctor_axioms_evars ctor' axioms'))
  end.

Ltac apply_spec_ctor_evars ctor spec :=
  lazymatch spec with
    | Spec_Axioms ?axioms => apply_spec_ctor_axioms_evars ctor axioms
    | Spec_Cons ?f ?T ?rest =>
      (raw_evar
         f T
         (fun evar =>
            let ctor' := constr:(ctor evar) in
            let spec' := constr:(rest evar) in
            let spec'' := eval hnf in spec' in
            apply_spec_ctor_evars ctor' spec''))
  end.

Ltac pushout_interp_helper :=
  lazymatch goal with
    | |- genmod_type (genspec_spec ?gspec) _ =>
      let spec := (eval hnf in (genspec_spec gspec)) in
      apply_spec_ctor_evars (genmod_ctor _ (genspec_model gspec)) spec
  end.

(* FIXME: need an appropriate error message if the unify fails... *)
Ltac pushout_tac :=
  (raw_evar
     "__Spec"%string Spec
     (fun evar =>
        refine (Build_GMPushout _ _ _ _ _ ?__Spec _ _ _)));
  intros __R __model __r;
  [ pushout_interp_helper | pushout_interp_helper |
    lazymatch goal with
      | |- ?m1 = ?m2 =>
        unify m1 m2
    end;
    instantiate_spec ?__Spec;
    apply eq_refl ].
