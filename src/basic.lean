/- This file contains various definitions and lemmas which don't fit anywhere else, or when there
  is not enough material to make its own file -/

import data.pfun data.set.finite data.nat.enat topology.basic
import tactic.fattribute
universes u v

axiom omitted {P : Prop} : P

notation `ℕ∞` := enat

def is_finite (α : Type*) : Prop := nonempty (fintype α) -- set.finite (set.univ : set α)

namespace subtype
attribute [extensionality] subtype.eq'

variables {α : Sort*} {p : α → Prop}

protected lemma subsingleton (h : ∃ x, ∀ y, p y → y = x) : subsingleton {x // p x} :=
begin
  rcases h with ⟨x, px⟩, constructor, rintro ⟨y, py⟩ ⟨z, pz⟩, ext,
  cases px y py, cases px z pz, refl
end

protected lemma subsingleton' (h : ∃! x, p x) : subsingleton {x // p x} :=
let ⟨x, px, qx⟩ := h in subtype.subsingleton ⟨x, qx⟩

protected lemma nonempty (h : ∃ x, p x) : nonempty {x // p x} :=
let ⟨x, hx⟩ := h in ⟨⟨x, hx⟩⟩

end subtype

namespace trunc
instance nonempty {α : Sort u} [h : nonempty α] : nonempty (trunc α) :=
let ⟨x⟩ := h in ⟨trunc.mk x⟩

end trunc

namespace classical
variables {α : Sort u} {β : Sort v} {p : α → Prop}
noncomputable def unique_choice : nonempty α ∧ subsingleton α → α :=
classical.choice ∘ and.left

noncomputable def unique_indefinite_description (p : α → Prop)
  (h : ∃! x, p x) : {x // p x} :=
unique_choice $ let ⟨x, px, qx⟩ := h in ⟨⟨⟨x, px⟩⟩, subtype.subsingleton' h⟩

noncomputable def the (p : α → Prop) (h : ∃! x, p x) : α :=
(unique_indefinite_description p h).1
lemma the_spec (h : ∃! x, p x) : p (the p h) :=
(unique_indefinite_description p h).2
lemma the_unique (h : ∃! x, p x) (y : α) (py : p y) : y = the p h :=
let ⟨x, px, qx⟩ := h in (qx y py).trans (qx _ (the_spec h)).symm

noncomputable def choose_trunc (h : nonempty α) : trunc α :=
unique_choice $ by split; apply_instance

open set
noncomputable def take_arbitrary {α β : Type*} (f : α → β) (h : nonempty α)
  (hf : ∀x y : α, f x = f y) : β :=
the (range f) $ let ⟨x⟩ := h in
  ⟨f x, mem_range_self x, λ y hy, let ⟨x', hx'⟩ := hy in hx'.symm.trans $ hf x' x⟩

noncomputable def take_arbitrary_in {α β : Type*} (s : set α) (f : α → β) (h : nonempty s)
  (hf : ∀x y ∈ s, f x = f y) : β :=
take_arbitrary (λ x : s, f x.1) (let ⟨⟨x, hx⟩⟩ := h in ⟨⟨x, hx⟩⟩) (λ⟨x, hx⟩ ⟨y, hy⟩, hf x y hx hy)

noncomputable def take_arbitrary_such_that {α β : Type*} {p : α → Prop} (f : α → β)
  (h : ∃ x, p x) (hf : ∀x y, p x → p y → f x = f y) : β :=
take_arbitrary_in {x | p x } f (let ⟨x, px⟩ := h in ⟨⟨x, px⟩⟩) hf

end classical

variables {α : Type*} {β : Type*}

noncomputable def roption.classical_to_option {α} (x : roption α) : option α :=
by haveI := classical.dec; exact x.to_option

namespace vector

def vector_one_equiv : vector α 1 ≃ α :=
{ to_fun := λ x, x.head,
  inv_fun := λ x, ⟨[x], dec_trivial⟩,
  left_inv := omitted,
  right_inv := omitted}

end vector

namespace set
lemma finite_of_subset_finset {s : set α} (t : finset α) (h : s ⊆ ↑t) : s.finite :=
finite_subset (finset.finite_to_set t) h

/-- The cardinality of any subset of a finite type. -/
noncomputable def cardinality [fintype α] (s : set α) : ℕ :=
by haveI := classical.dec; haveI := (set_fintype s); exact fintype.card s

end set

namespace finset

variables (r : α → α → Prop) [decidable_rel r] [is_trans α r] [is_antisymm α r] [is_total α r]

lemma sort_length [decidable_eq α] (s : finset α) : (sort r s).length = s.card :=
by rw [←list.to_finset_card_of_nodup (sort_nodup r s), sort_to_finset r s]

end finset


/-- the pullback of a relation along a function -/
-- cf. preorder_lift
def pullback_rel (f : α → β) (r : β → β → Prop) : α → α → Prop := λ x y, r (f x) (f y)
namespace pullback_rel
instance (f : α → β) (r : β → β → Prop) [is_trans β r] : is_trans α (pullback_rel f r) :=
⟨λ x y z h₁ h₂, (trans h₁ h₂ : r (f x) (f z))⟩

protected def is_antisymm (f : α → β) (r : β → β → Prop) (h : function.injective f)
  [is_antisymm β r] : is_antisymm α (pullback_rel f r) :=
⟨λ x y h₁ h₂, h $ antisymm h₁ h₂⟩

instance (f : α → β) (r : β → β → Prop) [is_total β r] : is_total α (pullback_rel f r) :=
⟨λ x y, total_of r (f x) (f y)⟩

instance (f : α → β) (r : β → β → Prop) [decidable_rel r] : decidable_rel (pullback_rel f r) :=
by dsimp [pullback_rel]; apply_instance
end pullback_rel

def is_maximal {α : Type*} [preorder α] (s : set α) (x : α) : Prop := x ∈ s ∧ ∀(y ∈ s), ¬y > x
def is_minimal {α : Type*} [preorder α] (s : set α) (x : α) : Prop := x ∈ s ∧ ∀(y ∈ s), ¬y < x