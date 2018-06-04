-- Kurzweil-Henstock gauge integration in R^n
-- following HOL-Light

import data.set meta_data data.list data.vector 
topology.real .complex algebra.big_operators algebra.module

noncomputable theory

open classical
open set vector nat real

local attribute [instance] prop_decidable

universe u
variable { α : Type u }

-- convert set of vector to vector of sets.
-- Gives a type error without let statement, m = succ m - 1.
def vs : Π {n : ℕ}, set (vector α n) → vector (set α) n  
| 0 s := ⟨[],by simp *⟩
| (succ m) s := 
let tail := (tail:vector α (succ m) → vector α m) in
 (head '' s) :: @vs m (tail '' s)

def finset.set_of (s : finset α) : set α :=
(λ x : α, x ∈ s)

variable { n : ℕ }

def closed_interval  (a : vector ℝ n) (b : vector ℝ n) : set (vector ℝ n) := 
{ x | ∀ i, a.nth i ≤ x.nth i ∧ x.nth i ≤ b.nth i }

local notation `⟦` a , b `⟧` := closed_interval a b  

variables (a : vector ℝ n) (b : vector ℝ n)

-- XX clean up.
constant top : topological_space (vector ℝ n)
instance : topological_space (vector ℝ n) := top
constant vectorspace : vector_space ℝ (vector ℝ n)
instance : vector_space ℝ (vector ℝ n) := vectorspace

def content (s: set(vector ℝ n)) : ℝ :=
if (s = ∅) then 0 
else list.prod (map (λ x, sup x - inf x) (vs s)).1

variable (d : vector ℝ n → set (vector ℝ n)) 
variable (s : finset (set (vector ℝ n)))
variable (p : finset(vector ℝ n × set (vector ℝ n)))

def gauge : Prop :=
(∀ x, x ∈ d x ∧ is_open (d x))

def division_of i :=
(∀ k ∈ s, k ≠ ∅ ∧ ∃ a b, k = ⟦ a,b ⟧) ∧
(∀ k₁ k₂, k₁ ∈ s ∧ k₂ ∈ s ∧ (k₁ ≠ k₂) →
  interior k₁ ∩ interior k₂ = ∅) ∧
(⋃₀ (finset.set_of s) = i)

def tagged_partial_division_of i :=
(∀ x k, (x,k) ∈ p → x ∈ k ∧ k ⊆ i ∧ (∃ a b, k = ⟦ a,b ⟧)) ∧
(∀ x1 k₁ x2 k₂, (x1,k₁) ∈ p ∧ (x2,k₂) ∈ p ∧ (x1,k₁) ≠ (x2,k₂)
→ interior k₁ ∩ interior k₂ = ∅)

def tagged_division_of i :=
(tagged_partial_division_of p i) ∧ 
(⋃₀ {k | ∃ x, (x,k) ∈ p} = i)

def fine :=
(∀ x k, (x,k) ∈ p → k ⊆ d x)

-- duplicate, remove
def norm {n : ℕ} (u : vector ℝ n) : ℝ :=
     real.sqrt (list.sum (to_list (map (real.pow 2) u)))

-- duplicate, remove
def ball {n :ℕ} (c : vector ℝ n) (r : ℝ) : set (vector ℝ n) :=
{ x | norm (x-c) < r }

variable { m : ℕ } 

def has_integral_compact_interval 
(f : vector ℝ n → vector ℝ m) (y : vector ℝ m) i :=
(∀ ε > 0, ∃ d, @gauge n d ∧
  ∀ p, @tagged_division_of n p i ∧ fine d p →
  @norm m (finset.sum p 
     (λ xk, let (x,k) := xk in (content k • f x ) - y)) < ε)

-- gauge integral
def has_integral
(f : vector ℝ n → vector ℝ m) (y : vector ℝ m) i :=
if (∃ a b, i = ⟦ a,b ⟧) then has_integral_compact_interval f y i
else 
  (∀ ε > 0, ∃ B > 0, ∀ a b, ball 0 B ⊆ ⟦ a,b ⟧ → 
    ∃ z, norm (z - y) < ε ∧ 
       has_integral_compact_interval 
          (λ x, if x ∈ i then f x else 0) z ⟦ a,b ⟧)

def integrable_on f i :=
(∃ y, @has_integral n m f y i)
