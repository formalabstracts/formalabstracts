/- Individual results that should be moved to mathlib. If there are many related results, put them in a separate file. -/

import .basic data.finsupp

universe variables u v
open function

/- move to logic -/
def ite_ne_neg {p : Prop} [h : decidable p] {α : Sort u} {x y : α} (h : ite p x y ≠ y) : p :=
by { by_cases hp : p, exact hp, rw [if_neg hp] at h, contradiction }

def ite_ne_pos {p : Prop} [h : decidable p] {α : Sort u} {x y : α} (h : ite p x y ≠ x) : ¬p :=
by { by_cases hp : p, rw [if_pos hp] at h, contradiction, exact hp }


namespace sum
lemma injective_inl {α β : Type*} : injective (inl : α → α ⊕ β) :=
λ x y, inl.inj

lemma injective_inr {α β : Type*} : injective (inr : β → α ⊕ β) :=
λ x y, inr.inj

def embedding_inl {α β : Type*} : α ↪ α ⊕ β :=
⟨inl, injective_inl⟩

def embedding_inr {α β : Type*} : β ↪ α ⊕ β :=
⟨inr, injective_inr⟩
end sum

namespace equiv

def equiv_embedding_fun {α β : Type*} : (α ≃ β) ↪ (α → β) :=
⟨equiv.to_fun, λ f g, eq_of_to_fun_eq⟩

end equiv

namespace finsupp
/- move to finsupp -/
lemma injective_emb_domain {α β γ : Type*} [has_zero γ] [decidable_eq β] (f : α ↪ β) :
  injective (emb_domain f : (α →₀ γ) → (β →₀ γ)) :=
omitted

def finsupp_embedding_finsupp_left {α β γ : Type*} [has_zero γ] [decidable_eq β] (f : α ↪ β) :
  (α →₀ γ) ↪ (β →₀ γ) :=
⟨λ g, emb_domain f g, injective_emb_domain f⟩
end finsupp