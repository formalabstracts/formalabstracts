/- various properties about pfun and roption -/

import basic data.pfun

open set

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

namespace roption

def compatible (o₁ o₂ : roption α) : Prop := ∀{{x y}}, x ∈ o₁ → y ∈ o₂ → x = y

namespace compatible
  variables {o₁ o₂ o₃ : roption α}
  infix ` =. `:50 := roption.compatible
  protected lemma compatible_of_eq {x y : α} (h : x = y) :
    compatible (roption.some x) (roption.some y) :=
  omitted
  protected lemma symm (h : o₁ =. o₂) : o₂ =. o₁ := λx y hx hy, (h hy hx).symm
  -- note: it is not transitive, probably good to use different notation
end compatible

end roption

namespace pfun

protected def empty (α β : Type*) : α →. β := λx, roption.none
protected def id : α →. α := pfun.lift id
protected def comp (g : β →. γ) (f : α →. β) : α →. γ := λx, roption.bind (f x) g
infix ` ∘. `:90 := pfun.comp

def to_subtype (p : α → Prop) : α →. subtype p := λx, ⟨p x, λ h, ⟨x, h⟩⟩

def compatible (f g : α →. β) : Prop := ∀x, f x =. g x

namespace compatible
  variables {f g h : α →. β}
  infix ` ~. `:50 := pfun.compatible
  protected lemma symm (h : f ~. g) : g ~. f := λx, (h x).symm
  -- note: it is not transitive, probably good to use different notation
end compatible

def restrict' (f : α →. β) (p : set α) : α →. β :=
pfun.restrict f (inter_subset_right p (dom f))

end pfun

/- a partial equivalence -/
open pfun
structure pequiv (α : Type*) (β : Type*) :=
(to_fun    : α →. β)
(inv_fun   : β →. α)
(dom_inv_fun : ∀{{x}} (hx : x ∈ dom to_fun), to_fun.fn x hx ∈ dom inv_fun)
(dom_to_fun : ∀{{y}} (hy : y ∈ dom inv_fun), inv_fun.fn y hy ∈ dom to_fun)
(left_inv  : inv_fun ∘. to_fun ~. pfun.id)
(right_inv : to_fun ∘. inv_fun ~. pfun.id)

infixr ` ≃. `:25 := pequiv

namespace equiv
def to_pequiv (e : α ≃ β) : α ≃. β :=
⟨e.to_fun, e.inv_fun, λx hx, trivial, λy hy, trivial, omitted, omitted⟩

def rfl : α ≃ α := equiv.refl α
end equiv

namespace pequiv

instance : has_coe (α ≃. β) (α →. β) := ⟨pequiv.to_fun⟩
protected def rfl : α ≃. α := equiv.rfl.to_pequiv
protected def refl (α) : α ≃. α := pequiv.rfl
protected def symm (e : α ≃. β) : β ≃. α :=
⟨e.inv_fun, e.to_fun, e.dom_to_fun, e.dom_inv_fun, e.right_inv, e.left_inv⟩
protected def trans (e₁ : α ≃. β) (e₂ : β ≃. γ) : α ≃. γ :=
⟨e₂.to_fun ∘. e₁.to_fun, e₁.inv_fun ∘. e₂.inv_fun, omitted, omitted, omitted, omitted⟩

def restrict' (e : α ≃. β) (p : set α) : α ≃. β :=
⟨e.to_fun.restrict' p, e.inv_fun.restrict' (e.to_fun.image p), omitted, omitted, omitted, omitted⟩

def subtype_pequiv (p : α → Prop) : subtype p ≃. α :=
⟨pfun.lift subtype.val, to_subtype p, omitted, omitted, omitted, omitted⟩

end pequiv
