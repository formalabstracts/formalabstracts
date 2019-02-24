/-
Copyright (c) 2019 Jesse Han. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Han

Some goodies for reducing tactic goals to only data obligations with `omitted`

`omitted` tries to close a propositional goal with `exact omitted`

`omit_props` tries to close any visible goals with `exact omitted`

`tidy_with_omitted` runs `tidy` and lets it use `omitted` (and still produces proof traces)
-/

import data.set.finite tactic.tidy

axiom omitted {P : Prop} : P

section omitted_tactics
open tactic

/-- Check if the goal is a proposition; if so, prove it using omitted.

    When called with "tidy using omitted", tidy will run as usual and fulfill all
    proof obligations using omitted, leaving it to the user to specify the data. -/
meta def tactic.interactive.omitted : tactic unit :=
  do f <- (target >>= is_prop),
    if f then `[exact omitted]
         else tactic.fail "Goal is not a proposition and cannot be omitted"

meta def tactic.interactive.omit_props : tactic unit := `[all_goals {try {omitted}}]

meta def tactic.verbose_omitted : tactic string := tactic.interactive.omitted >> return "omitted"

open tactic.tidy

meta structure omitted_cfg :=
(trace_result : bool            := ff)
(trace_result_prefix : string   := "/- `tidy` says -/ ")
(tactics : list (tactic string) := default_tactics ++ [tactic.verbose_omitted])

meta def cfg_of_omitted_cfg : omitted_cfg → cfg :=
λ X, { trace_result := X.trace_result,
  trace_result_prefix := X.trace_result_prefix,
  tactics := X.tactics }

/- Calls tidy, but with `omitted` thrown into the tactic list.

  tidy {trace_result := tt}` produces a proof trace as usual.-/
meta def tactic.interactive.tidy_with_omitted (cfg : omitted_cfg := {}): tactic unit :=
tidy (cfg_of_omitted_cfg cfg)

end omitted_tactics

section test

variable {α : Type*}
open vector
example : vector α 1 ≃ α :=
begin
 split, omit_props,
 from λ x, ⟨[x], dec_trivial⟩,
 from λ x, x.head
end

example : vector α 1 ≃ α :=
begin
 tidy_with_omitted -- {trace_result := tt}
 , cases a_val, cases a_property, exact a_val_hd, exact [a]
end

end test
