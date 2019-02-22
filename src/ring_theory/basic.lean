import ..basic .algebra2

noncomputable theory
universes u v w
variables {α : Type*} {β : Type*} [comm_ring α] [comm_ring β]

open set

/-- An element in a ring is nilpotent if a integer power of it is equal to `0` -/
def is_nilpotent {α : Type u} [comm_semiring α] (x : α) : Prop := ∃ n : ℕ, x^n = 0
/-- An ring is reduced if `0` is its only nilpotent element -/
def is_reduced (α : Type u) [comm_semiring α] : Prop := ∀(x : α), is_nilpotent x → x = 0
/-- A ring is algebraically closed if every non-constant polynomial has a root in α -/
def is_algebraically_closed (α : Type u) [comm_semiring α] [decidable_eq α] : Prop :=
∀(p : polynomial α), p.degree > 0 → ∃x, p.is_root x

namespace ideal

/-- An ideal is radical if it is equal to its radical -/
def is_radical {α : Type u} [comm_ring α] (I : ideal α) : Prop := I = I.radical
/-- The type of maximal ideals in a ring -/
@[reducible] def maximal_ideal (α : Type u) [comm_ring α] : Type u :=
subtype (ideal.is_maximal : ideal α → Prop)
/-- The type of prime ideals in a ring -/
@[reducible] def prime_ideal (α : Type u) [comm_ring α] : Type u :=
subtype (ideal.is_prime : ideal α → Prop)
/-- The type of radical ideals in a ring -/
@[reducible] def radical_ideal (α : Type u) [comm_ring α] : Type u :=
subtype (ideal.is_radical : ideal α → Prop)

/-- An ideal where the quotient forms a field is a maximal ideal -/
lemma is_maximal_of_field {I : ideal α}
  (h1 : has_inv I.quotient)
  (h2 : zero_ne_one_class I.quotient)
  (h3 : ∀{a : I.quotient}, a ≠ 0 → a * a⁻¹ = 1)
  (h4 : ∀{a : I.quotient}, a ≠ 0 → a⁻¹ * a = 1) : is_maximal I :=
omitted

/-- The kernel of a ring homomorphism -/
protected def ker (f : α → β) [is_ring_hom f] : ideal α :=
linear_map.ker (alg_hom.of_ring_hom f).to_linear_map

/-- `x` is an element of the kernel of `f` iff `f x = 0` -/
@[simp] lemma mem_ker (f : α → β) [is_ring_hom f] {x : α} : x ∈ ideal.ker f ↔ f x = 0 :=
linear_map.mem_ker

/-- The quotient of a ring by a radical ideal is reduced. -/
lemma is_reduced_quotient {I : ideal α} (h : I.is_radical) : is_reduced (quotient I) :=
omitted

/-- the map f → range f is a ring homomorphism -/
instance range_factorization.is_ring_hom (f : α → β) [is_ring_hom f] :
  is_ring_hom (range_factorization f) :=
begin
  constructor; intros; apply subtype.eq; simp [range_factorization],
  rw [is_ring_hom.map_one f], refl,
  rw [is_ring_hom.map_mul f], refl,
  rw [is_ring_hom.map_add f], refl
end

/-- the map out of the quotient of the kernel to the range of a map -/
def quotient_ker_map (f : α → β) [is_ring_hom f] : (ideal.ker f).quotient → range f :=
by { haveI : is_ring_hom (range_factorization f) := by apply_instance,
     apply quotient.lift _ (range_factorization f), intros a h,
     apply subtype.eq, rw [ideal.mem_ker] at h, exact h }

/-- The map above is a ring homomorphism -/
instance quotient_ker_map.is_ring_hom (f : α → β) [is_ring_hom f] :
  is_ring_hom (quotient_ker_map f) :=
by { haveI : is_ring_hom (range_factorization f) := by apply_instance,
     dsimp [quotient_ker_map], apply_instance }

/- the inverse map to the above map -/
def quotient_ker_inv (f : α → β) [is_ring_hom f] : range f → (ideal.ker f).quotient :=
λ x, ideal.quotient.mk (ideal.ker f) (classical.some x.property)

/-- The maps above form an equivalence -/
def quotient_ker_equiv (f : α → β) [is_ring_hom f] : (ideal.ker f).quotient ≃ range f :=
⟨quotient_ker_map f, quotient_ker_inv f, omitted, omitted⟩

/- To do: Every field is a subfield of an algebraically closed field -/

end ideal

