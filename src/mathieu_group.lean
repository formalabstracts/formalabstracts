import group_theory.basic
import data.finset group_theory.group_action

open finset fintype is_monoid_action

universes u v

local attribute [instance, priority 0] classical.prop_decidable

variables {α : Type u} {β : Type v} (t k v : ℕ) 

/- 
A Steiner system $S(t,k,v)$, where $t < k < v$ are positive integers is a finite set $X$ of cardinality $v$, a collection of $k$ element subsets of $X$ (called blocks), such that each $t$ element subset of $X$ is contained in a unique block.
-/
structure steiner_system (t k v : ℕ) :=
(X : Type u) 
(blocks : finset (finset X))
(h₁ : fintype X)
(h₂ : card X = v)
(h₃ : ∀ b ∈ blocks, card b = k)
(h₄ : ∀ x : finset X, card x = t → ∃! b ∈ blocks, x ⊂ b)

/- The underlying set of a steiner system is finite. -/
instance steiner_system_fintype (s : steiner_system t k v) : fintype s.X := s.h₁

/- The set of all isomorphisms of between two steiner systems consists of all equivalences of the underlying sets which are block-preserving. -/
def steiner_system_isomorphism 
{t₁ k₁ v₁ : ℕ} 
{t₂ k₂ v₂ : ℕ}
(s₁ : steiner_system t₁ k₁ v₁)
(s₂ : steiner_system t₂ k₂ v₂) := {f : s₁.X ≃ s₂.X | ∀ b ∈ s₁.blocks, finset.image f b ∈ s₂.blocks }

/- The automorphism set $\mathrm{Aut}(s)$ of a steiner system $s$ is the set of isomorphisms from $s$ to $s$. -/
def Aut {t k v : ℕ}(s : steiner_system t k v) := steiner_system_isomorphism s s

/- The automorphism set of a steiner system can be equipped with a group structure with group identity the identity function, multiplication is function composition, inverses are function inverses. -/
instance {s : steiner_system t k v} : group (Aut s) := 
by
refine { 
   one := ⟨equiv.refl s.X, omitted⟩  ,
   mul := fun f g, ⟨f.1.trans g.1, omitted⟩,
   inv := fun f, ⟨ equiv.symm f.1, omitted⟩, 
   one_mul := omitted,
   mul_one := omitted,
   mul_left_inv := omitted, 
   mul_assoc := omitted,
} 

/- The Steiner system $S(5,8,24)$ exists and is unique up to isomorphism.-/
lemma is_unique_s_5_8_24 : ∃ x: steiner_system 5 8 24, ∀ y : steiner_system 5 8 24, nonempty $ steiner_system_isomorphism x y := omitted 

/- Using the axiom of choice, we can pick a representative of the isomorphism class of $S(5,8,24)$.-/
noncomputable def s_5_8_24 : steiner_system 5 8 24 := 
classical.some is_unique_s_5_8_24


/- The Steiner system $S(5,6,12)$ exists and is unique up to isomorphism.-/
lemma is_unique_s_5_6_12 : ∃ x: steiner_system 5 6 12, ∀ y : steiner_system 5 6 12, nonempty $ steiner_system_isomorphism x y := omitted 

/- Using the axiom of choice, we can pick a representative of the isomorphism class of $S(5,6,12)$.-/
noncomputable def s_5_6_12 : steiner_system 5 6 12 := classical.some is_unique_s_5_6_12  

/- The automorphism group of a steiner system acts on the underlying set through the evaluation action.-/
def evaluation_action {t k v : ℕ} (s : steiner_system t k v):
Aut(s) → s.X → s.X := (λ f x, f.1 x)

/- The evaluation action of the automorphism group satisfies the properties of a monoid action. -/
instance {t k v : ℕ} (s : steiner_system t k v) : is_monoid_action (evaluation_action s) := omitted 

/---- *TODO(Kody) : move these to mathlib?*----/
variables [monoid α] (f : α → β → β) [is_monoid_action f]

/- The two point stabilizer of a group is the set of all group elements which fix two distinct points of the group via the group action. -/
def two_pt_stabilizer (x ∈ {y : β × β | y.1 ≠ y.2}): set α :=
{ y : α | f y x.1 = x.1 ∧ f y x.2 = x.2}

/- The stabilizer of a group is a subgroup of the group. -/
instance is_subgroup_stabilizer [group α] (f : α → β → β) [is_monoid_action f] (a : β) : is_subgroup(stabilizer f a)
:= omitted 


/- The two point stabilizer of a group is a subgroup of the group. -/
instance is_subgroup_two_pt_stabilizer [group α](f : α → β → β)
[is_monoid_action f] (x ∈ {y : β × β | y.1 ≠ y.2}) : is_subgroup(two_pt_stabilizer f x (by {assumption})) := omitted
/----------------------------------------------/

/-The group $M_{11}$ is the stabilizer of an arbitrary point of the steiner system $S(5,6,12)$ under the evaluation action of its Automorphism group.-/
def M11 := stabilizer (evaluation_action s_5_6_12) (classical.choice (by {rw ← fintype.card_pos_iff, rw  s_5_6_12.h₂, exact dec_trivial}))

/-The group $M_{12}$ is the automorphism group of the steiner system $S(5,6,12)$.-/
def M12 := Aut(s_5_6_12)

/- The group $M_{23}$ is the stabilizer of an arbitrary point of the steiner system $S(5,8,24)$ under the evaluation action of its automorphism group.-/
def M23 := stabilizer (evaluation_action s_5_8_24) (classical.choice (by {rw ← fintype.card_pos_iff, rw s_5_8_24.h₂,exact dec_trivial}))

/- The group $M_{22}$ is the stabilizer of two arbitrary points of the steiner system $S(5,8,24)$ under the evaluation action of its automorphism group. -/
/- TODO : prove you can pick two elements by choice. -/
def M22 := two_pt_stabilizer (evaluation_action s_5_8_24) (classical.choice (omitted)) 

/- The group $M_{24}$ is the automorphism group of the steiner system $S(5,8,24)$. -/
def M24 := Aut(s_5_8_24) 
