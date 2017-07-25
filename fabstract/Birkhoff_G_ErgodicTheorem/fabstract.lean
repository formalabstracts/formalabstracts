import folklore.measure_theory 
noncomputable theory
open set real_axiom.extended_real

namespace Birkhoff_G_ErgodicTheorem

variables {X : Type} (σ : set (set X)) [sigma_algebra σ] (μ : set X → ℝ∞) [hms : measure_space σ μ]

def measure_preserving (T : X → X) := ∀ s ∈ σ, μ (image T s) = μ s

def {u} function.pow {α : Type u} (f : α → α) : ℕ → (α → α)
| 0 := id
| (n+1) := f ∘ (function.pow n)

def {u} nth_preimage {α : Type u} (f : α → α) : ℕ → (set α → set α)
| 0 := id
| (n+1) := λ s, {a | f a ∈ nth_preimage n s}

variable (T : X → X)

def ergodic [finite_measure_space σ μ] := ∀ E ∈ σ, nth_preimage T 1 E = E → μ E = 0 ∨ μ E = of_real (univ_measure σ μ)

variables (f : X → ℝ) [lebesgue_integrable σ μ f]

include hms
def time_average_partial (x : X) : ℕ → ℝ :=
(λ n, (1/n)*((((list.iota n).map (λ k, f (function.pow T k x)))).foldr (+) 0))

def time_average_exists (x : X) : Prop :=
nat_limit_at_infinity_exists (time_average_partial σ μ T f x)

def time_average (x : X) : ℝ := 
nat_limit_at_infinity (time_average_partial σ μ T f x)
omit hms

def space_average [finite_measure_space σ μ] [lebesgue_integrable σ μ f] := (1/univ_measure σ μ)*lebesgue_integral σ μ f


unfinished Birkhoffs_ergodic_theorem :
    ∀ {X} {σ : set (set X)} {μ} [sigma_algebra σ] [finite_measure_space σ μ],
    ∀ (f : X → ℝ) [lebesgue_integrable σ μ f], 
    ∀ {T : X → X} (t_mp : measure_preserving σ μ T) (t_erg : ergodic σ μ T),
         almost_everywhere σ μ (λ x : X, time_average_exists σ μ T f x ∧ time_average σ μ T f x = space_average σ μ f) :=
{description := "Birkhoff's ergodic theorem."}

def fabstract : meta_data :=
{description := "Birkhoff's ergodic theorem states that, under appropriate conditions, the space average of an integrable function f is equal to the time average of f wrt a measure preserting transformation T. This result was proved in a slightly different form by Birkhoff (1931), and stated and proved in this form by many others, including Halmos (1960) and Furstenberg (1981).",
authors := [{name := "George Birkhoff"}],
primary := cite.DOI "10.1073/pnas.17.2.656",
results := [result.Proof @Birkhoffs_ergodic_theorem]
}


end  Birkhoff_G_ErgodicTheorem
