/- 
Frechet derivatives on Banach space

Reference: Garrett's notes
http://www-users.math.umn.edu/~garrett/m/fun/Notes/01_spaces_fcns.pdf
-/

import order.filter data.set meta_data data.list data.vector
       .real_axiom algebra.module data.finset.basic .metric
       .complex

noncomputable theory

namespace derivatives

open set filter classical nat int list vector real_axiom metric finset complex

local attribute [instance] prop_decidable

universes u v w

variables {α : Type u} { β : Type u}

class complex_vector_space β extends vector_space ℂ β

class  normed_space β extends complex_vector_space β :=
(norm : β → ℝ)
(positivity : ∀ v, norm v ≥ 0)
(norm0 : ∀ v, norm v = 0 ↔ v = 0)
-- (homogeneity : ∀ (c : ℂ) (v : β), norm(c • v) = complex.norm c * norm v)
(triangle_inequality : ∀ v w, norm(v + w) ≤ norm v + norm w)

variables (c : ℂ) (v : β) [p : normed_space β]

#check c • v












end derivatives
