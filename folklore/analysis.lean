import .real_axiom
open classical real_axiom
local attribute [instance] prop_decidable
noncomputable theory

-- This will all be made obsolete once Lean 3 has a proper analysis library.
-- In Lean 2, limits were defined much more generally using filters.

def real_approaches_at (f : ℝ → ℝ) (a b : ℝ) : Prop :=
∀ ε > 0, ∃ δ, ∀ x, 0 < abs (x - a) → abs (x - a) < δ → abs (f x - b) < ε

def real_approaches_at_infinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ x > N, abs (f x - b) < ε

def nat_approaches_at_infinity (f : ℕ → ℝ) (b : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ x > N, abs (f x - b) < ε


def real_limit_at_infinity_exists (f : ℝ → ℝ) : Prop :=
∃ b, real_approaches_at_infinity f b

def real_limit_at_infinity (f : ℝ → ℝ) : ℝ :=
if h : real_limit_at_infinity_exists f then some h
else 0


def nat_limit_at_infinity_exists (f : ℕ → ℝ) : Prop :=
∃ b, nat_approaches_at_infinity f b

def nat_limit_at_infinity (f : ℕ → ℝ) : ℝ :=
if h : nat_limit_at_infinity_exists f then some h
else 0
