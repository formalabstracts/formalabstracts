import .basic
import tactic.depends
import data.finset group_theory.group_action

open finset fintype is_monoid_action

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

lemma is_unique_s_5_8_24 : ∀ x y : steiner_system 5 8 24, steiner_system_isomorphism x y := sorry 

lemma s_5_6_12 : steiner_system 5 6 12 := sorry 

lemma is_unique_s_5_6_12 : ∀ x y : steiner_system 5 6 12, steiner_system_isomorphism x y := sorry 

def map_action {t k v : ℕ} (s : steiner_system t k v):
Aut(s) → s.X → s.X :=
begin
intros f x, 
exact f.map x,
end

instance {t k v : ℕ} (s : steiner_system t k v) : is_monoid_action (map_action s) := sorry 

def M11 (x : s_5_6_12.X):= stabilizer (map_action s_5_6_12) x
def M12 := Aut(s_5_6_12) 
def M22 : unit := sorry
def M23 (x : s_5_8_24.X):= stabilizer (map_action s_5_8_24) x
def M24 := Aut(s_5_8_24) 

-- #check is_monoid_action.stabilizer $ map_action s  


#depends M24
#depends steiner_system_isomorphism
#depends steiner_system.blocks
#check @is_monoid_action.stabilizer