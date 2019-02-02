import group_theory.basic
import data.finset group_theory.group_action
import category_theory.category

open finset fintype is_monoid_action

universes u v

local attribute [instance, priority 0] classical.prop_decidable

variables {α : Type u} {β : Type v} (t k v : ℕ) 

structure steiner_system (t k v : ℕ) :=
(X : Type u) 
(blocks : finset (finset X))
(h₁ : fintype X)
(h₂ : card X = v)
(h₃ : ∀ b ∈ blocks, card b = k)
(h₄ : ∀ x : finset X, card x = t → ∃! b ∈ blocks, x ⊂ b)

instance steiner_system_fintype (s : steiner_system t k v) : fintype s.X := s.h₁

structure steiner_system_isomorphism {t₁ k₁ v₁ : ℕ} (s₁ : steiner_system t₁ k₁ v₁)
{t₂ k₂ v₂ : ℕ}
(s₂ : steiner_system t₂ k₂ v₂)
:=
(map : s₁.X ≃ s₂.X)
(h₁ : ∀ b ∈ s₁.blocks, finset.image map b ∈ s₂.blocks)

variable s : steiner_system t k v

def Aut {t k v : ℕ}(s : steiner_system t k v) := steiner_system_isomorphism s s  

instance {s : steiner_system t k v} : group (Aut s) := 
by
 refine { 
   one := id,
   mul := function.comp _ _, 
   inv := function.inv_fun _,  
   one_mul := function.comp.left_id, 
   mul_one := function.comp.right_id, 
   mul_left_inv := function.inv_fun_comp,
   mul_assoc := sorry
   } 

lemma is_unique_s_5_8_24 : ∃ x: steiner_system 5 8 24, ∀ y : steiner_system 5 8 24, nonempty $ steiner_system_isomorphism x y := omitted 

noncomputable def s_5_8_24 : steiner_system 5 8 24 := 
classical.some is_unique_s_5_8_24

lemma is_unique_s_5_6_12 : ∃ x: steiner_system 5 6 12, ∀ y : steiner_system 5 6 12, nonempty $ steiner_system_isomorphism x y := omitted 

noncomputable def s_5_6_12 : steiner_system 5 6 12 := classical.some is_unique_s_5_6_12  

def evaluation_action {t k v : ℕ} (s : steiner_system t k v):
Aut(s) → s.X → s.X :=
begin
intros f x, 
exact f.map x,
end

instance {t k v : ℕ} (s : steiner_system t k v) : is_monoid_action (evaluation_action s) := omitted 

instance is_subgroup_stabilizer [group α] (f : α → β → β) [is_monoid_action f] (a : β) : is_subgroup(stabilizer f a)
:= omitted 

def M11 := stabilizer (evaluation_action s_5_6_12) (classical.choice (by {rw ← fintype.card_pos_iff, rw  s_5_6_12.h₂, exact dec_trivial}))

def M12 : Group := Aut(s_5_6_12) 
def M22 : Group := sorry
def M23 (x : s_5_8_24.X):= stabilizer (evaluation_action s_5_8_24) x
def M24 := Aut(s_5_8_24) 

-- #check is_monoid_action.stabilizer $ evaluation_action s  


#depends M24
#depends steiner_system_isomorphism
#depends steiner_system.blocks
#check @is_monoid_action.stabilizer