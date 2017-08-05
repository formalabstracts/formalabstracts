import meta_data

namespace Szemeredi_Lemma

def injective { α β : Type } ( f : α → β ) : Prop := ∀ x y : α, (f x = f y) → (x = y)

private def subset_of_0_until_N_with_at_least_m_elements ( N m : ℕ ) ( P : fin N → Prop ) : Prop :=
∃ f : fin m → { x // P x }, injective f

private def contains_arithmetic_progression_of_length' ( P : ℕ → Prop ) ( k : ℕ ) : Prop :=
∃ n : ℕ, ∃ r > 1, ∀ i < k, P(n + i * r)

private def contains_arithmetic_progression_of_length { N : ℕ } ( P : fin N → Prop ) ( k : ℕ ) : Prop :=
contains_arithmetic_progression_of_length' (λ n, dite (n < N) (λ w, P ⟨ n, w ⟩ ) (λ w, false) ) k

axiom Szemeredi_Lemma :
∀ k n : ℕ, 
  ∃ N : ℕ, 
    ∀ P : fin N → Prop, 
      subset_of_0_until_N_with_at_least_m_elements N (N/n) P → contains_arithmetic_progression_of_length P k

definition fabstract : meta_data :=
{ description := "A finitary statement of Szemerédi's lemma (that a subset of the natural numbers with positive upper density contains an arithmetic progression of any length).",
  authors := [
    {name := "Endre Szemerédi"}
  ],
  primary := cite.URL "https://zbmath.org/?q=an:0303.10056",
  results := [result.Proof Szemeredi_Lemma] }

end Szemeredi_Lemma
