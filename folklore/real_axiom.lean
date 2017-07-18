/-
axiomatic development of the complete ordered field
of real numbers in classical logic.

At some point this should be replaced with an actual
construction.

T.Hales, July 15, 2017
-/

import data.list data.vector 

noncomputable theory

namespace real_axiom

open classical nat int list vector

universe u

constant ℝ : Type u
constant real_of_int : ℤ → ℝ
def real_0 := real_of_int 0
def real_1 := real_of_int 1

constant real_add : ℝ → ℝ → ℝ
constant real_sub : ℝ → ℝ → ℝ
constant real_neg : ℝ → ℝ
constant real_mul : ℝ → ℝ → ℝ
constant real_div : ℝ → ℝ → ℝ
constant real_inv : ℝ → ℝ
constant real_lt : ℝ → ℝ → Prop
constant sup : (set ℝ) → ℝ

instance real_of_nat_coe : has_coe ℤ ℝ :=
⟨ real_of_int ⟩


instance real_has_lt : has_lt ℝ :=
  ⟨ real_lt ⟩ 
def real_le (x : ℝ) (y : ℝ) := x < y ∨ x = y
instance real_has_zero : has_zero ℝ :=
  ⟨ real_0 ⟩
instance has_real_one : has_one ℝ :=
  ⟨ real_1 ⟩
instance real_has_neg : has_neg ℝ :=
 ⟨ real_neg ⟩
instance real_has_add : has_add ℝ :=
 ⟨ real_add ⟩
instance real_has_mul : has_mul ℝ :=
 ⟨ real_mul ⟩
instance real_has_div : has_div ℝ :=
 ⟨ real_div ⟩
instance real_has_inv : has_inv ℝ :=
 ⟨ real_inv ⟩
instance real_has_sub : has_sub ℝ :=
 ⟨ real_sub ⟩
instance real_has_le : has_le ℝ :=
 ⟨ real_le  ⟩

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
 (dedekind_completeness : (∀ (S : set α), (S≠ ∅) → has_upper_bound S → 
  is_least_upper_bound S (sup S)))

axiom real_dedekind_completeness :
(∀ (S : set ℝ), (S≠ ∅) → has_upper_bound S → 
  is_least_upper_bound S (sup S))

instance real_complete_ordered_field : complete_ordered_field ℝ :=
{
real_axiom.real_ordered_field with
sup := sup,
dedekind_completeness := real_dedekind_completeness
}

axiom real_archimedean :
(∀ x y, x > 0 → y > 0 → ∃ (n : ℕ), y < n*x)

-- why does -x ∈ S fail?
-- why does {x | ... } fail?

def real_inf (S : set ℝ) : ℝ := 
- (sup (λ x, S( -x )))

-- extension by zero when x < 0.
def real_sqrt (x : ℝ) : ℝ :=
   sup (λ (t : ℝ), (t = 0) ∨ t*t = x)

def real_abs (x : ℝ) : ℝ :=
  sup (λ (t : ℝ),  t = x ∨ t = -x)

def real_max (x : ℝ) y : ℝ :=
  sup (λ (t : ℝ), t = x ∨ t = y)

def real_min (x : ℝ) y : ℝ :=
  real_inf (λ (t : ℝ), t = x ∨ t = y)

def real_pow : ℝ → ℕ → ℝ
 | x 0 :=  (1 : ℝ)
 | x (succ n) := x * (real_pow x n)

local infix `^` := real_pow

-- alternating series for pi/4  = 1 - 1/3 + 1/5 -...
constant pi : ℝ

axiom pi_def : 
(∀ (n : nat), 
  let iota := list.iota n,
      terms := list.map (λ k, (-1)^(k+1) / (2*k-1)) iota in
  (real_abs (pi/ 4 - list.sum terms)  < 1 / (2*n + 3)))


end real_axiom

