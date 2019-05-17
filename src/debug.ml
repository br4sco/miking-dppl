(** Debugging utilities *)

open Printf
open Utest

(** Debug the input term *)
let debug_input = true

(** Debug the labelling *)
let debug_label = false

(** Debug the static analysis *)
let debug_sanalysis = false

(** Debug the resample transformation *)
let debug_resample_transform = false

(** Debug the CPS transformation *)
let debug_cps = true

(** Debug SMC inference *)
let debug_smc = true

(** Debug dynamic SMC inference *)
let debug_smc_dyn = false

(** Debug the evaluation *)
let debug_eval = false

(** Debug applications when evaluating *)
let debug_eval_app = false

(** Debug the evaluation environment *)
let debug_eval_env = false

(** Debug printout *)
let debug cond heading info =
  if cond && not !utest then begin
    printf "--- %s ---\n" (String.uppercase_ascii heading);
    printf "%s\n\n%!" (info ());
  end
