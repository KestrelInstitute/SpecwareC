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

Ltac start_refinement :=
  (raw_evar
     "__Spec"%string Spec
     (fun evar =>
        refine (Build_GMRefinement _ ?__Spec _)));
  intros __R __model __r;
  econstructor; constructor.
