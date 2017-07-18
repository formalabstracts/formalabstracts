/-
axiomatic development of the complete ordered field
of real numbers in classical logic.

At some point this should be replaced with an actual
construction.

T.Hales, July 15, 2017
-/

import meta_data
import data.list data.vector

noncomputable theory

namespace real_axiom

open classical nat int list vector

universe u

-- TODO: This definition used to be universe-polymorphic, but it looks like unfinished
-- does not support parameters so the universe u is unavailable, fix it.
unfinished ℝ : Type :=
{ description := "the type real numbers" }

unfinished real_of_int : ℤ → ℝ :=
{ description := "the canonical embedding of integers into reals" }

-- TODO: properly treat unbounded and empty sets
unfinished sup : (set ℝ) → ℝ :=
{ description := "the supremum of a subset of real numbers" }

instance real_of_nat_coe : has_coe ℤ ℝ :=
⟨ real_of_int ⟩

@[instance] constant real_ordered_field : linear_ordered_field ℝ

-- It is not clear why this line is required; but it is.
attribute [instance] real_ordered_field

def is_upper_bound {α : Type u} [R : linear_ordered_ring α] (S : set α) (r : α) : Prop :=
  (∀ (s : α), s ∈ S  → s ≤ r)

def has_upper_bound {α : Type u} [R : linear_ordered_ring α] (S : set α) : Prop :=
  (∃ r : α, is_upper_bound S r)

def is_least_upper_bound {α : Type u} [R : linear_ordered_ring α] (S : set α) (s : α) :=
  (is_upper_bound S s ∧
  (∀ r, is_upper_bound S r → r ≤ s))


class complete_ordered_field (α : Type u) extends linear_ordered_field α :=
 (sup : (set α) → α)
 (dedekind_completeness : (∀ (S : set α), (S ≠ ∅) → has_upper_bound S →
  is_least_upper_bound S (sup S)))

unfinished real_dedekind_completeness :
  (∀ (S : set ℝ), (S ≠ ∅) → has_upper_bound S →
    is_least_upper_bound S (sup S)) :=
{ description := "the real numbers are Dedekind complete" }

instance real_complete_ordered_field : complete_ordered_field ℝ :=
{
real_axiom.real_ordered_field with
sup := sup,
dedekind_completeness := real_dedekind_completeness
}

unfinished real_archimedean :
  (∀ x y, x > 0 → y > 0 → ∃ (n : ℕ), y < n*x) :=
{ description := "the real numbers are an archimedean field" }

-- why does -x ∈ S fail?
-- why does {x | ... } fail?

def real_inf (S : set ℝ) : ℝ :=
- (sup (λ x, S( -x )))

-- extension by zero when x < 0.
def real_sqrt (x : ℝ) : ℝ :=
   sup (λ (t : ℝ), (t = 0) ∨ t*t = x)

def real_abs (x : ℝ) : ℝ :=
  sup (λ (t : ℝ), t = x ∨ t = -x)

def real_max (x : ℝ) y : ℝ :=
  sup (λ (t : ℝ), t = x ∨ t = y)

def real_min (x : ℝ) y : ℝ :=
  real_inf (λ (t : ℝ), t = x ∨ t = y)

def real_pow : ℝ → ℕ → ℝ
 | x 0 :=  (1 : ℝ)
 | x (succ n) := x * (real_pow x n)

local infix `^` := real_pow

unfinished pi : ℝ :=
{ description := "the ratio of the circumference and the diameter of a circle" }

-- one possible specification of pi
unfinished pi_def :
  (∀ (n : nat),
    let iota := list.iota n,
        terms := list.map (λ k, (-1)^(k+1) / (2*k-1)) iota in
    (real_abs (pi/ 4 - list.sum terms)  < 1 / (2*n + 3))) :=
{ description := "alternating series for pi/4  = 1 - 1/3 + 1/5 -..." }

end real_axiom
