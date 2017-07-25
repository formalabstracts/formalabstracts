import .real_axiom .analysis
open set classical real_axiom real_axiom.extended_real
local attribute [instance] prop_decidable
noncomputable theory

def countable_union {X : Type} (f : ℕ → set X) : set X := 
{x | ∃ n, x ∈ f n}

variables {X : Type} (σ : set (set X))
class sigma_algebra :=
(univ_mem : univ ∈ σ)
(closed_under_comp : ∀ s, s ∈ σ → univ \ s ∈ σ)
(closed_under_countable_union : ∀ f : ℕ → set X, (∀ n, f n ∈ σ) → countable_union f ∈ σ)

variable [sigma_algebra σ]

-- alternatively, we could define μ using subtypes, as a function {s : set X // s ∈ σ} → ℝ∞.
class measure_space (μ : (set X) → ℝ∞) :=
(measure_nonneg : ∀ s ∈ σ, μ s ≥ 0)
(measure_empty : μ ∅ = 0)
(measure_union : ∀ (f : ℕ → set X), (∀ n, f n ∈ σ) → (∀ m n, m ≠ n → f m ∩ f n = ∅) →
   μ (countable_union f) = extended_real.countable_sum (μ ∘ f))

class finite_measure_space (μ : (set X) → ℝ∞) extends measure_space σ μ :=
(measure_univ_finite : ∃ b : ℝ, μ univ = of_real b)

def univ_measure (μ : (set X) → ℝ∞) [finite_measure_space σ μ] : ℝ := 
some (@finite_measure_space.measure_univ_finite X σ (by apply_instance) μ (by apply_instance))

def lebesgue_measurable (f : X → ℝ) :=
∀ t : ℝ, {x | f x > t} ∈ σ

-- note that we assume μ is a total function here. Theorems involving μ should assume the arguments are in σ.
variable μ : (set X) → ℝ∞

section
variable [measure_space σ μ]

-- this assumes s ∈ σ
def indicator_measure (s : set X) : ℝ∞ := μ s

def indicator_function (s : set X) (x : X) : ℝ := if x ∈ s then 1 else 0

def is_simple_function (ls : list (ℝ × (set X))) := ∀ p : ℝ × (set X), p ∈ ls → p.1 ≥ 0 ∧ p.2 ∈ σ

def simple_function (ls : list (ℝ × (set X))) (x : X) : ℝ := 
(ls.map (λ p : ℝ × (set X), p.1 * indicator_function p.2 x)).foldr (+) 0

-- must use 0*∞ = 0
-- this assumes is_simple_function ls
def simple_function_integral (ls : list (ℝ × (set X))) : ℝ∞ :=
(ls.map (λ p : ℝ × (set X), of_real p.1 * indicator_measure μ p.2)).foldr (+) 0

-- this will be better looking once we have better parsing for unfinished
unfinished simple_function_integral_well_defined :
 ∀ {X μ σ} [sigma_algebra σ] [measure_space σ μ] (ls1 : list (ℝ × set X)) (ls2 : list (ℝ × set X)),  
    (∀ p : ℝ × (set X), p ∈ ls1 → p.1 ≥ 0 ∧ p.2 ∈ σ) → (∀ p : ℝ × (set X), p ∈ ls2 → p.1 ≥ 0 ∧ p.2 ∈ σ) → 
      (lebesgue_measurable σ (simple_function ls1)) → (lebesgue_measurable σ (simple_function ls2)) → 
        (simple_function ls1 = simple_function ls2) → (simple_function_integral μ ls1 = simple_function_integral μ ls2) :=
{ description := "the integral of a simple function does not depend on the representation of that function" }

-- assumes for (h : ∀ x, f x ≥ 0)
-- wiki defines this with f : X → ℝ∞ . why?
def nonneg_function_integral (f : X → ℝ) : ℝ∞ :=
extended_real.sup 
  (image (simple_function_integral μ) 
   {ls : list (ℝ × (set X)) | is_simple_function σ ls ∧ ∀ x, 0 ≤ simple_function ls x ∧  (simple_function ls x) ≤ f x})

-- this shorter version should work when unfinished is fixed
/-unfinished simple_function_integral_eq_nonneg_function_integral :
 ∀ {X μ σ} [sigma_algebra σ] [measure_space σ μ] (ls : list (ℝ × set X)),
    (∀ p : ℝ × (set X), p ∈ ls → p.1 ≥ 0 ∧ p.2 ∈ σ) → (lebesgue_measurable σ (simple_function ls)) →
     simple_function_integral μ ls = nonneg_function_integral σ μ (simple_function ls) :=
{ description := "the simple and nonnegative integrals match" }-/
unfinished simple_function_integral_eq_nonneg_function_integral :
 ∀ {X μ σ} [sigma_algebra σ] [measure_space σ μ] (ls : list (ℝ × set X)),
    (∀ p : ℝ × (set X), p ∈ ls → p.1 ≥ 0 ∧ p.2 ∈ σ) → (lebesgue_measurable σ (simple_function ls)) →
     simple_function_integral μ ls = @nonneg_function_integral _ σ _ μ (by apply_instance) (simple_function ls) :=
{ description := "the simple and nonnegative integrals match" }

def pos_part (f : X → ℝ) (x : X) : ℝ := if f x > 0 then f x else 0
def neg_part (f : X → ℝ) (x : X) : ℝ := if f x < 0 then -(f x) else 0

theorem pos_part_nonneg (f : X → ℝ) (x : X) : pos_part f x ≥ 0 :=
begin cases (em (f x > 0)), all_goals {unfold pos_part, simp *}, {apply le_of_lt, assumption}, apply le_refl end

theorem neg_part_nonneg (f : X → ℝ) (x : X) : neg_part f x ≥ 0 :=
begin cases (em (f x < 0)), all_goals {unfold neg_part, simp *}, {apply le_of_lt, apply neg_pos_of_neg, assumption}, apply le_refl end

unfinished pos_part_plus_neg_part : ∀ {X} (f : X → ℝ) (x : X), abs (f x) = pos_part f x + neg_part f x :=
{ description := "abs f decomposes into the sum of pos and neg parts" }

-- assumes nonneg_function_integral (pos_part f) < ∞ or nonneg_function_integral (neg_part f) < ∞

def signed_integral_exists_condition (f : X → ℝ) := nonneg_function_integral σ μ (pos_part f) < inf ∨ nonneg_function_integral σ μ (neg_part f) < inf

-- assumes signed_integral_exists_condition f
def signed_function_integral (f : X → ℝ) : ℝ∞ :=
nonneg_function_integral σ μ (pos_part f) + nonneg_function_integral σ μ (neg_part f)

class lebesgue_integrable (f : X → ℝ) :=
(r : ℝ) (f_integrable : signed_integral_exists_condition σ μ f) (integral_value : signed_function_integral σ μ f = of_real r)

def lebesgue_integral (f : X → ℝ) [lebesgue_integrable σ μ f] : ℝ := @lebesgue_integrable.r X σ (by apply_instance) μ (by apply_instance) f (by apply_instance)

def almost_everywhere (P : X → Prop) := {x | ¬ P x} ∈ σ ∧ μ {x | ¬ P x} = 0

end
