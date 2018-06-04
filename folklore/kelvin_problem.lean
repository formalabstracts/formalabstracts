/-
Kelvin Problem for minimal foams.

The statement of the precise conjecture was developed by
T. Hales, R. Kusner, F. Morgan, and J. Sullivan, 2017
building on a long history of work on the Kelvin problem,
especially the Weaire-Phelan construction of a counterexample
to the original Kelvin problem.

-/

import data.set meta_data data.list data.vector .real_axiom

noncomputable theory

namespace kelvin_problem

open set classical nat int list vector real_axiom

local attribute [instance] prop_decidable

universes u v w

variables {α : Type} { β : Type}

variables (σ : set (set ℝ))

def sigma_algebra_contains_open_sets := 
(∀ t : ℝ, { x | x < t } ∈ σ)




end kelvin_problem
