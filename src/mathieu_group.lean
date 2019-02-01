import .basic
import data.finset 

open finset fintype

universe u 

local attribute [instance] classical.prop_decidable

variables {α : Type u} (t k v : ℕ) 

structure steiner_system (t k v : ℕ) :=
(X : Type u) 
(blocks : finset (finset X))
(h₁ : fintype X)
(h₂ : card X = v)
(h₃ : ∀ b ∈ blocks, card b = k)
(h₄ : ∀ x : finset X, card x = t → ∃! b ∈ blocks, x ⊂ b)

structure steiner_system_isomorphism {t₁ k₁ v₁ : ℕ} (s₁ : steiner_system t₁ k₁ v₁)
{t₂ k₂ v₂ : ℕ}
(s₂ : steiner_system t₂ k₂ v₂)
:=
(map : s₁.X ≃ s₂.X)
(h₁ : ∀ b ∈ s₁.blocks, finset.image map b ∈ s₂.blocks)

variable s : steiner_system t k v

def Aut {t k v : ℕ}(s : steiner_system t k v) := steiner_system_isomorphism s s  

instance {s : steiner_system t k v} : group (Aut s) := sorry
-- by refine { one := _, inv := _, mul := _, .. }; obviously 

lemma s_5_8_24 : steiner_system 5 8 24 := sorry 

lemma s_5_6_12 : steiner_system 5 6 12 := sorry 

def M24 : Aut(s_5_8_24) := sorry 
def M12 : Aut(s_5_6_12) := sorry 


